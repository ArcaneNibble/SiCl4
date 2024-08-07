//! Concurrent hashtable very much inspired by WebKit's WTF::ParkingLot
//!
//! This is used to set aside work items that cannot run because they are
//! not able to acquire needed locks. The items will only be re-queued when
//! locks get released. Maps (address (of a _graph_ node) + generation) -> (list of work item)
//!
//! Unlike in WebKit, this is specifically designed for our specific set of
//! reader-writer locks (which either have or don't have priority).
//! In the case where there is no priority, the map only stores a list of
//! "interested in the lock, couldn't get it, set aside until the lock is released"
//! work items. In the case where there _is_ priority, the map _additionally_
//! stores a list of lock holders. There can be at most one write lock holder,
//! but there can be many read lock holders. This is needed so that speculative
//! work which has been invalidated can be found so that it can be cancelled.
//! As an optimization, the "no priority" executor does not use this.
//!
//! Also unlike in WebKit, the maximum size is not O(threads) but can be
//! as large as O(netlist) in pathological cases, so resizing cannot be
//! as expensive. Maximum parallelism is still bounded however (as this is
//! hardcoded into other parts of the code such as the allocator) so
//! we can still make assumptions about the amount of concurrent accesses.
//! Because of this, we use sharding vaguely inspired by Java ConcurrentHashMap.
//!
//! When a work item blocks on a lock, we don't want to suspend OS threads.
//! We will likely be able to find some other work item to try to do.
//! In general, it is not expected that threads ever block on I/O
//! but are instead just busy doing some computation.
//! As a result, we currently don't ever bother with OS locks
//! but instead just spin forever. TODO: PROFILE THIS
//!
//! This is self-deprecatingly called a stroad because it tries to
//! keep work items moving but often just turns into a parking lot nonetheless.
//!
//! ```text
//! +--------------------+           +---------------------------+
//! | Shard 0 | lock_bit |  -->      | buckets (resizable array) |
//! +--------------------+           | - wants_lock_list         |  -->     doubly-linked list of nodes
//! | Shard 1 | lock_bit |           | - holds_lock_list         |  -->     doubly-linked list of nodes
//! +--------------------+           +---------------------------+
//! | Shard ...          |           | ...                       |
//! +--------------------+           +---------------------------+
//! | Shard n | lock_bit |
//! +--------------------+
//! ```
//!
//! The head of the linked lists (i.e. the bucket contents) have `next`
//! pointing to the first node, and `prev` pointing to the last node.
//! The last node has `next` pointing to None, and the first node
//! has `prev` pointing to None (this avoids a nasty type cast).
//!
//! ```text
//!        Bucket           Entry 0               Entry n
//!      +--------+       +---------+           +---------+
//!      | next   |  -->  | next    |  --...->  | next    |  -X->
//!  /-  | prev   |  -X-  | prev    |  <-...--  | prev    |  <-\
//!  |   +--------+       +---------+           +---------+    |
//!  \----->---------------->--------------------->------------/
//! ```
//!
//! Hashes are broken up as follows:
//! ```text
//! +-msb---------------------lsb-+
//! | unused | bucket # | shard # |
//! +-----------------------------+
//! ```
//! The number of bits used for the shard index never changes, but
//! the number of bits used for the bucket index does.
use std::{
    alloc::{self, Layout},
    cell::UnsafeCell,
    fmt::Debug,
    hash::{Hash, Hasher},
    marker::PhantomData,
    ops::{Deref, DerefMut},
    ptr::{slice_from_raw_parts, slice_from_raw_parts_mut},
    sync::atomic::Ordering,
};

use crate::util::to_unsafecell;
use crate::{executor_engine::WorkQueueInterface, loom_testing::*};

use super::TypeErasedObjRef;

/// When a lock is being acquired and released, said operations need
/// the ability to reach back "up" to unpark or cancel other work items.
/// Due to the way we've built the abstractions, it has to be possible to
/// _reach_ said work items from linked list nodes. This trait provides that link.
///
/// This will be called, with the bucket lock held,
/// on the thread that released the lock triggering the unpark/cancel.
/// This thread will be an "other" thread, i.e. *not* the thread which
/// is potentially actively working on the work item. These methods must
/// internally synchronize s.t. this is safe.
///
/// This can be called from multiple threads at the same time!
/// Methods _must_ be safe to call from multiple threads, must be idempotent,
/// and "cancel" must win over "unpark".
// TODO: add "get priority" here maybe??? (difference is one pointer indirection)
pub trait WorkItemInterface: Send + Sync {
    type WorkItemTy;

    /// The given work item is now possible to attempt to run again
    ///
    /// Used for both ordered and unordered algorithms
    ///
    /// Called only once, after the thread working on the work item fails to grab a lock.
    /// However, it can be called at the same time as the working thread is
    /// still trying to release the locks it has successfully speculatively acquired.
    fn unpark<Q: WorkQueueInterface<WorkItemTy = Self::WorkItemTy>>(&self, onto_q: &mut Q);

    /// The given work item has been invalidated by some other access
    ///
    /// Used only for ordered algorithms
    ///
    /// This can be called from multiple threads at the same time
    /// (e.g. work item holds two speculative locks, both get cancelled due to *two*
    /// higher-priority work items)
    fn cancel<Q: WorkQueueInterface<WorkItemTy = Self::WorkItemTy>>(&self, onto_q: &mut Q);
}

/// log2 of the number of toplevel shards
///
/// Birthday paradox formula: want to find `d` s.t.
/// `1 - Π_{k=1}^{n-1} (1 - k/d) <= some threshold we pick`
/// (where n = MAX_THREADS)
///
/// for our purposes, pick arbitrarily n = 64, threshold = 10%,
/// and we will use the approximation of
/// `1 - ((d - 1) / d)^{(n(n - 1)) / 2} <= 0.10`
///
/// `((d - 1) / d)^2016 >= 0.90`
///
/// `d ~>= 19135`
///
/// now round it to a power of 2
const HASH_NUM_SHARDS_SHIFT: usize = 15;
/// Number of toplevel shards
const HASH_NUM_SHARDS: usize = 1 << HASH_NUM_SHARDS_SHIFT;

/// log2 of the number of initial buckets
// 2 64-bit pointer size but ehhhhh also handwavey
const BUCKETS_INITIAL_ENT_SHIFT: usize = 1;
/// Number of initial buckets
const BUCKETS_INITIAL_ENT: usize = 1 << BUCKETS_INITIAL_ENT_SHIFT;
const _: () = debug_assert!(BUCKETS_INITIAL_ENT_SHIFT >= 1);

/// hash using [rustc_hash::FxHasher]
fn hash<'arena>(key: TypeErasedObjRef<'arena>) -> u64 {
    let mut hasher = rustc_hash::FxHasher::default();
    key.hash(&mut hasher);
    hasher.finish()
}

/// Type alias for linked list pointers
type ListEntryPtr<'stroad_node, 'arena, P> =
    Option<&'stroad_node UnsafeCell<StroadNode<'stroad_node, 'arena, P>>>;
/// Doubly-linked list links
struct DoubleLL<'stroad_node, 'arena, P> {
    next: ListEntryPtr<'stroad_node, 'arena, P>,
    prev: ListEntryPtr<'stroad_node, 'arena, P>,
}
// safety: note that this isn't Send/Sync and doesn't need to be
// -- there are no useful methods on this type, and all of the useful methods are on Stroad
impl<'stroad_node, 'arena, P> Debug for DoubleLL<'stroad_node, 'arena, P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DoubleLL")
            .field("next", &self.next.map(|x| x.get()))
            .field("prev", &self.prev.map(|x| x.get()))
            .finish()
    }
}
/// Hashtable entry nodes, which happen to correspond to locks in the upper layers
///
/// Some notes on lifetimes, references, and pinning:
/// * Fields other than `link` are read-only after initialization (and are thus freely sharable).
///     * `prio` will get written one more time before trying to do an ordered lock
/// * In general, we treat these node/state objects as unmovable, although moving technically
///   should work if the node isn't on any linked lists.
///     * The invariant lifetime trick is used for this.
/// * `&mut` is used to indicate that this node isn't on any linked lists.
///     * A `&mut` reference implies that it is the *only* reference to that object
/// * Because a [Stroad] is annotated that it borrows items with lifetime `'stroad_node`,
///   accepting a `&'stroad_node mut` tells the borrow checker that the passed-in items
///   can no longer be used by the calling code.
pub struct StroadNode<'stroad_node, 'arena, P> {
    /// linked list next
    link: DoubleLL<'stroad_node, 'arena, P>,
    /// hash key
    pub key: TypeErasedObjRef<'arena>,
    /// task priority
    ///
    /// negative is a writer, smaller absolute value is higher priority
    pub prio: i64,
    /// A link to get the work item from this node
    pub work_item_link: P,
}
impl<'stroad_node, 'arena, P> StroadNode<'stroad_node, 'arena, P> {
    /// Initialize in place, *EXCEPT* the external work item link
    pub unsafe fn init(self_: *mut Self, obj: TypeErasedObjRef<'arena>) {
        (*self_).link = DoubleLL {
            next: None,
            prev: None,
        };
        (*self_).key = obj;
        (*self_).prio = 0;
    }
}
impl<'stroad_node, 'arena, P: Debug> Debug for StroadNode<'stroad_node, 'arena, P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StroadNode")
            .field("@addr", &(self as *const _))
            .field("link", &self.link)
            .field("key", &self.key)
            .field("prio", &self.prio)
            .field("work_item_link", &self.work_item_link)
            .finish()
    }
}

/// One single hash bucket entry
struct StroadBucket<'stroad_node, 'arena, P> {
    /// Lock instances wanting a lock
    wants_lock: DoubleLL<'stroad_node, 'arena, P>,
    /// Lock instances holding a lock
    holds_lock: DoubleLL<'stroad_node, 'arena, P>,
}
// safety for all blocks in this struct:
// it is only possible for a &mut StroadBucket to be created
// through a &mut StroadShard, where we have guaranteed
// that we are the only thread accessing any of the list items
impl<'stroad_node, 'arena, P> StroadBucket<'stroad_node, 'arena, P> {
    pub fn link_at_head(
        &mut self,
        stroad_node: &'stroad_node UnsafeCell<StroadNode<'stroad_node, 'arena, P>>,
        holding_lock: bool,
    ) {
        let list_head = if holding_lock {
            &mut self.holds_lock
        } else {
            &mut self.wants_lock
        };

        unsafe {
            (*(stroad_node.get())).link.next = list_head.next;
            (*(stroad_node.get())).link.prev = None;
        }
        if let Some(next) = list_head.next {
            unsafe {
                (*(next.get())).link.prev = Some(stroad_node);
            }
        }

        list_head.next = Some(stroad_node);
        if list_head.prev.is_none() {
            list_head.prev = Some(stroad_node);
        }
    }

    pub fn link_at_tail(
        &mut self,
        stroad_node: &'stroad_node UnsafeCell<StroadNode<'stroad_node, 'arena, P>>,
        holding_lock: bool,
    ) {
        let list_head = if holding_lock {
            &mut self.holds_lock
        } else {
            &mut self.wants_lock
        };

        unsafe {
            (*(stroad_node.get())).link.prev = list_head.prev;
            (*(stroad_node.get())).link.next = None;
        }
        if let Some(prev) = list_head.prev {
            unsafe {
                (*(prev.get())).link.next = Some(stroad_node);
            }
        }

        list_head.prev = Some(stroad_node);
        if list_head.next.is_none() {
            list_head.next = Some(stroad_node);
        }
    }

    pub fn unlink_item(
        &mut self,
        stroad_node: &'stroad_node UnsafeCell<StroadNode<'stroad_node, 'arena, P>>,
        holding_lock: bool,
    ) {
        let list_head = if holding_lock {
            &mut self.holds_lock
        } else {
            &mut self.wants_lock
        };

        unsafe {
            if let Some(prev) = (*(stroad_node.get())).link.prev {
                (*(prev.get())).link.next = (*(stroad_node.get())).link.next;
            } else {
                // entry 0
                list_head.next = (*(stroad_node.get())).link.next;
            }
            if let Some(next) = (*(stroad_node.get())).link.next {
                (*(next.get())).link.prev = (*(stroad_node.get())).link.prev;
            } else {
                // entry n
                list_head.prev = (*(stroad_node.get())).link.prev;
            }
        }
    }
}
impl<'stroad_node, 'arena, P> Debug for StroadBucket<'stroad_node, 'arena, P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StroadBucket")
            .field("@addr", &(self as *const _))
            .field("wants_lock", &self.wants_lock)
            .field("holds_lock", &self.holds_lock)
            .finish()
    }
}

/// One single hash map shard (out of [HASH_NUM_SHARDS])
///
/// All methods *require* the bucket lock to already be held
/// (i.e. access through [StroadShardGuard])
struct StroadShard<'stroad_node, 'arena, P> {
    /// Owning pointer to an array of [StroadBucket]
    buckets_and_lock: AtomicUsize,
    /// Number of entries in this shard
    nents: usize,
    /// log2 of the size of the bucket array
    capacity_shift: usize,
    _p: PhantomData<StroadBucket<'stroad_node, 'arena, P>>,
}
impl<'stroad_node, 'arena, P> Debug for StroadShard<'stroad_node, 'arena, P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StroadShard")
            .field("@addr", &(self as *const _))
            // we *don't know* that we have the lock held, so don't go into buckets
            .field(
                "buckets_and_lock",
                &(self.buckets_and_lock.load(Ordering::Relaxed) as *const ()),
            )
            .field("nents", &self.nents)
            .field("capacity_shift", &self.capacity_shift)
            .finish()
    }
}
impl<'stroad_node, 'arena, P: WorkItemInterface> StroadShard<'stroad_node, 'arena, P> {
    /// Insert the lock instance onto either the [wants_lock](StroadBucket::wants_lock)
    /// or [holds_lock](StroadBucket::holds_lock) list
    ///
    /// Returns a downgraded shared reference to the item
    pub fn insert<'stroad>(
        &'stroad mut self,
        stroad_node: &'stroad_node mut StroadNode<'stroad_node, 'arena, P>,
        hash: u64,
        holding_lock: bool,
    ) -> &'stroad_node StroadNode<'stroad_node, 'arena, P> {
        let buckets_ptr_usz = self.buckets_and_lock.load(Ordering::Relaxed) & !1;
        let mut buckets_ptr = buckets_ptr_usz as *mut StroadBucket<'stroad_node, 'arena, P>;

        if buckets_ptr.is_null() {
            let layout =
                Layout::array::<StroadBucket<'stroad_node, 'arena, P>>(BUCKETS_INITIAL_ENT)
                    .unwrap();
            unsafe {
                // safety: we "know" that all zeros is a valid init
                let new_buckets = alloc::alloc_zeroed(layout);
                self.capacity_shift = BUCKETS_INITIAL_ENT_SHIFT;
                buckets_ptr = new_buckets as *mut _;
            }
            self.buckets_and_lock
                .store(buckets_ptr as usize | 1, Ordering::Relaxed);
        }

        if self.nents >= 1 << (self.capacity_shift - 1) {
            buckets_ptr = self.resize_buckets(buckets_ptr);
        }

        let bucket_i = (hash >> HASH_NUM_SHARDS_SHIFT) & ((1 << self.capacity_shift) - 1);
        let bucket = unsafe {
            // safety: this is the size of the buckets array
            // (which this shard exclusively owns)
            let buckets = &mut *slice_from_raw_parts_mut(buckets_ptr, 1 << self.capacity_shift);
            &mut buckets[bucket_i as usize]
        };
        bucket.link_at_head(to_unsafecell(stroad_node), holding_lock);

        self.nents += 1;
        stroad_node
    }

    /// Double the size of the hash bucket array (and rehash everything)
    fn resize_buckets<'stroad>(
        &'stroad mut self,
        old_buckets_ptr: *mut StroadBucket<'stroad_node, 'arena, P>,
    ) -> *mut StroadBucket<'stroad_node, 'arena, P> {
        let old_layout =
            Layout::array::<StroadBucket<'stroad_node, 'arena, P>>(1 << self.capacity_shift)
                .unwrap();
        self.capacity_shift += 1;
        let new_layout =
            Layout::array::<StroadBucket<'stroad_node, 'arena, P>>(1 << self.capacity_shift)
                .unwrap();
        let new_buckets_ptr = unsafe {
            let new_buckets = alloc::alloc_zeroed(new_layout);
            new_buckets as *mut StroadBucket<'stroad_node, 'arena, P>
        };
        let (old_buckets, new_buckets) = unsafe {
            // safety: this is the size of the buckets array
            // (which this shard exclusively owns)
            (
                &mut *slice_from_raw_parts_mut(old_buckets_ptr, 1 << (self.capacity_shift - 1)),
                &mut *slice_from_raw_parts_mut(new_buckets_ptr, 1 << self.capacity_shift),
            )
        };
        for old_bucket_i in 0..old_buckets.len() {
            let mut list_ent = old_buckets[old_bucket_i].holds_lock.next;
            while let Some(list_ent_) = list_ent {
                // safety: when a lock instance is parked/owned, we take in a &'stroad_node mut
                // but only release a &'stroad_node (non-mut) back to external code
                // (so external code can't modify anything anymore).
                // the only time when a &mut is created again is when unparking
                // or cancelling, in which case only a single thread can be performing
                // that operation (because we've taken the bucket/shard lock),
                // and also we ensure that we've unlinked it before creating the &mut
                let list_ent_ref = unsafe { &*list_ent_.get() };
                let hash = hash(list_ent_ref.key);
                let new_bucket_i =
                    (hash >> HASH_NUM_SHARDS_SHIFT) & ((1 << self.capacity_shift) - 1);

                let next = list_ent_ref.link.next;
                new_buckets[new_bucket_i as usize].link_at_tail(list_ent_, true);
                list_ent = next;
            }

            let mut list_ent = old_buckets[old_bucket_i].wants_lock.next;
            while let Some(list_ent_) = list_ent {
                // safety: see above
                let list_ent_ref = unsafe { &*list_ent_.get() };
                let hash = hash(list_ent_ref.key);
                let new_bucket_i =
                    (hash >> HASH_NUM_SHARDS_SHIFT) & ((1 << self.capacity_shift) - 1);

                let next = list_ent_ref.link.next;
                new_buckets[new_bucket_i as usize].link_at_tail(list_ent_, false);
                list_ent = next;
            }
        }
        self.buckets_and_lock
            .store(new_buckets_ptr as usize | 1, Ordering::Relaxed);
        unsafe {
            // safety: we have transferred out all of the data,
            // so we won't access it again
            alloc::dealloc(old_buckets_ptr as *mut u8, old_layout);
        }
        new_buckets_ptr
    }

    /// Unpark all items on the [wants_lock](StroadBucket::wants_lock) list
    ///
    /// This is used for the unordered case
    pub fn unpark_all<Q: WorkQueueInterface<WorkItemTy = P::WorkItemTy>>(
        &mut self,
        key: TypeErasedObjRef<'arena>,
        hash: u64,
        onto_q: &mut Q,
    ) {
        let buckets = self.buckets_and_lock.load(Ordering::Relaxed) & !1;
        let buckets = buckets as *mut StroadBucket<'stroad_node, 'arena, P>;
        let bucket_i = (hash >> HASH_NUM_SHARDS_SHIFT) & ((1 << self.capacity_shift) - 1);

        if buckets.is_null() {
            return;
        }

        let bucket = unsafe {
            // safety: this is the size of the buckets array
            // (which this shard exclusively owns)
            let buckets = &mut *slice_from_raw_parts_mut(buckets, 1 << self.capacity_shift);
            &mut buckets[bucket_i as usize]
        };
        let mut list_ent = bucket.wants_lock.next;
        while let Some(list_ent_) = list_ent {
            // safety: see above in resize_buckets
            let list_ent_ref = unsafe { &*list_ent_.get() };
            if list_ent_ref.key == key {
                list_ent = list_ent_ref.link.next;
                bucket.unlink_item(list_ent_, false);
                // only at this point, after unlink, do we know that nothing else
                // is referencing the node
                let list_ent_mut = unsafe { &mut *list_ent_.get() };
                list_ent_mut.work_item_link.unpark(onto_q);
                self.nents -= 1;
            } else {
                list_ent = list_ent_ref.link.next;
            }
        }
    }
}

/// RAII guard locking one single shard of the hash map
struct StroadShardGuard<'stroad, 'stroad_node, 'arena, P>(
    &'stroad mut StroadShard<'stroad_node, 'arena, P>,
);
impl<'stroad, 'stroad_node, 'arena, P> Debug
    for StroadShardGuard<'stroad, 'stroad_node, 'arena, P>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // because we know we have the lock held, we can print all the things
        let mut dbg = f.debug_struct("StroadShardGuard");
        dbg.field("@p", &(self.0 as *const _));
        let buckets = self.0.buckets_and_lock.load(Ordering::Relaxed) & !1;
        let buckets = buckets as *const StroadBucket<'stroad_node, 'arena, P>;
        unsafe {
            // safety: this is the size of the buckets array
            // (which this shard exclusively owns)
            let buckets = &*slice_from_raw_parts(buckets, 1 << self.capacity_shift);
            dbg.field("<buckets>", &buckets);
        }
        dbg.field("nents", &self.nents);
        dbg.field("capacity_shift", &self.capacity_shift);
        dbg.finish()
    }
}
impl<'stroad, 'stroad_node, 'arena, P> Drop for StroadShardGuard<'stroad, 'stroad_node, 'arena, P> {
    fn drop(&mut self) {
        self.0.buckets_and_lock.fetch_and(!1, Ordering::Release);
    }
}
impl<'stroad, 'stroad_node, 'arena, P> Deref
    for StroadShardGuard<'stroad, 'stroad_node, 'arena, P>
{
    type Target = StroadShard<'stroad_node, 'arena, P>;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}
impl<'stroad, 'stroad_node, 'arena, P> DerefMut
    for StroadShardGuard<'stroad, 'stroad_node, 'arena, P>
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0
    }
}

/// Stroad hash map
pub struct Stroad<'stroad_node, 'arena, P> {
    /// Array of shards
    shards: [UnsafeCell<StroadShard<'stroad_node, 'arena, P>>; HASH_NUM_SHARDS],
}
// safety: we are using interior mutability with locking,
// so the locks guarantee that only one thread is accessing a given shard at once
//
// we can shift around ownership of stuff between threads in many operations, so
// --> require Send on K (and P)
//
// we can compute hashes and unpark/cancel simultaneously from different threads
// (see notes on the trait) --> require Sync on K (and P)
unsafe impl<'stroad_node, 'arena, P: WorkItemInterface> Sync for Stroad<'stroad_node, 'arena, P> {}
impl<'stroad_node, 'arena, P> Debug for Stroad<'stroad_node, 'arena, P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut dbg = f.debug_struct("Stroad");
        for i in 0..HASH_NUM_SHARDS {
            dbg.field(
                &format!("shards[{i}]"),
                // fixme: this may data race?
                &(unsafe { &*self.shards[i].get() }),
            );
        }
        dbg.finish()
    }
}
impl<'stroad_node, 'arena, P: WorkItemInterface> Stroad<'stroad_node, 'arena, P> {
    /// Allocate a new hash map
    ///
    /// Always returns a box because it overflows the stack otherwise
    pub fn new() -> Box<Self> {
        unsafe {
            let self_ = alloc::alloc_zeroed(Layout::new::<Self>()) as *mut Self;
            #[cfg(loom)]
            {
                // need to init AtomicUsize
                for i in 0..HASH_NUM_SHARDS {
                    (*(*self_).shards[i].get()).buckets_and_lock = AtomicUsize::new(0);
                }
            }
            // safety: we "know" that all zeros is a valid init
            Box::from_raw(self_)
        }
    }

    /// For an unordered algorithm, perform the park operation
    /// (blocking the work item) onto the [wants_lock](StroadBucket::wants_lock) list
    pub fn unordered_park_conditionally<VAL>(
        &self,
        stroad_node: &'stroad_node mut StroadNode<'stroad_node, 'arena, P>,
        validation: VAL,
    ) -> Result<
        &'stroad_node StroadNode<'stroad_node, 'arena, P>,
        &'stroad_node mut StroadNode<'stroad_node, 'arena, P>,
    >
    where
        VAL: FnOnce() -> bool,
    {
        let hash = hash(stroad_node.key);
        let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
        let mut shard = self.lock_shard(shard as usize);

        // lock held, call validation
        let should_park = validation();
        if !should_park {
            return Err(stroad_node);
        }

        let ret = shard.insert(stroad_node, hash, false);
        Ok(ret)
    }

    /// For an ordered algorithm, unblock all the work items
    pub fn unordered_unpark_all<Q: WorkQueueInterface<WorkItemTy = P::WorkItemTy>>(
        &self,
        key: TypeErasedObjRef<'arena>,
        onto_q: &mut Q,
    ) {
        let hash = hash(key);
        let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
        let mut shard = self.lock_shard(shard as usize);
        shard.unpark_all(key, hash, onto_q);
    }

    /// Lock a given shard, returning a guard that allows access to it from the current (OS) thread only
    fn lock_shard<'stroad>(
        &'stroad self,
        shard_i: usize,
    ) -> StroadShardGuard<'stroad, 'stroad_node, 'arena, P> {
        let mut _spins = 0;
        let shard = self.shards[shard_i].get();
        'outer_spin: loop {
            // safety: atomic
            let mut old_ptr = unsafe { (*shard).buckets_and_lock.load(Ordering::Relaxed) };
            loop {
                if old_ptr & 1 != 0 {
                    _spins += 1;
                    spin_hint();
                    continue 'outer_spin;
                }
                let new_ptr = old_ptr | 1;
                // safety: atomic
                match unsafe {
                    (*shard).buckets_and_lock.compare_exchange_weak(
                        old_ptr,
                        new_ptr,
                        Ordering::Acquire,
                        Ordering::Relaxed,
                    )
                } {
                    Ok(_) => unsafe {
                        // safety: we just guaranteed we're the only one who can make a &mut
                        return StroadShardGuard(&mut *shard);
                    },
                    Err(x) => old_ptr = x,
                }
            }
        }
    }

    /// For an ordered algorithm, grab the hash lock, go through all the locks,
    /// abort other work items if necessary, and eventually return whether we're allowed to run
    ///
    /// Calls the `mark_item` callback with the bucket lock held upon success
    pub fn ordered_do_locking<MARK, Q: WorkQueueInterface<WorkItemTy = P::WorkItemTy>>(
        &self,
        stroad_node: &'stroad_node mut StroadNode<'stroad_node, 'arena, P>,
        prio: i64,
        mark_item: MARK,
        cancel_q: &mut Q,
    ) -> (bool, &'stroad_node StroadNode<'stroad_node, 'arena, P>)
    where
        MARK: FnOnce(),
    {
        let mut lock_okay = true;
        stroad_node.prio = prio;

        let key = stroad_node.key;
        let hash = hash(key);
        let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
        let mut shard = self.lock_shard(shard as usize);
        // shard lock held now, so we can get the bucket
        // fixme layering?
        let bucket_i = (hash >> HASH_NUM_SHARDS_SHIFT) & ((1 << shard.capacity_shift) - 1);
        let buckets_ptr_usz = shard.buckets_and_lock.load(Ordering::Relaxed) & !1;
        if buckets_ptr_usz == 0 {
            // there isn't even a bucket, so nobody has a lock, so fast path claim
            mark_item();
            return (true, shard.insert(stroad_node, hash, true));
        }
        let buckets_ptr = buckets_ptr_usz as *mut StroadBucket<'stroad_node, 'arena, P>;
        let bucket = unsafe {
            // safety: this is the size of the buckets array
            // (which this shard exclusively owns)
            let buckets = &mut *slice_from_raw_parts_mut(buckets_ptr, 1 << shard.capacity_shift);
            &mut buckets[bucket_i as usize]
        };

        if prio < 0 {
            // is a writer
            let prio = -(prio + 1);

            // a writer is okay as long as there are no other writers
            // *and* if there are no readers with the *same* priority

            // loop once, mostly looking for a conflicting writer but
            // also for readers of the same priority.
            // don't actually commit to cancelling anything yet, until
            // we *know* we're going to steal the lock
            let mut list_ent: Option<&UnsafeCell<StroadNode<'_, '_, P>>> = bucket.holds_lock.next;
            while let Some(list_ent_) = list_ent {
                // safety: see above in resize_buckets
                let list_ent_ref = unsafe { &*list_ent_.get() };
                if list_ent_ref.key == key {
                    if list_ent_ref.prio < 0 {
                        let other_prio = -(list_ent_ref.prio + 1);
                        if other_prio <= prio {
                            lock_okay = false;
                            break;
                        }
                        list_ent = list_ent_ref.link.next;
                    } else {
                        let other_prio = list_ent_ref.prio;
                        if prio == other_prio {
                            lock_okay = false;
                            break;
                        }
                        list_ent = list_ent_ref.link.next;
                    }
                }
            }

            // we have to loop twice, because we don't want to start canceling
            // readers unless we *know* we're going to take the write lock
            if lock_okay {
                let mut list_ent: Option<&UnsafeCell<StroadNode<'_, '_, P>>> =
                    bucket.holds_lock.next;
                while let Some(list_ent_) = list_ent {
                    // safety: see above
                    let list_ent_ref = unsafe { &*list_ent_.get() };
                    if list_ent_ref.key == key {
                        if list_ent_ref.prio < 0 {
                            let other_prio = -(list_ent_ref.prio + 1);
                            debug_assert!(prio < other_prio);
                            list_ent = list_ent_ref.link.next;
                            bucket.unlink_item(list_ent_, true);
                            // only at this point, after unlink, do we know that nothing else
                            // is referencing the node
                            let list_ent_mut = unsafe { &mut *list_ent_.get() };
                            list_ent_mut.work_item_link.cancel(cancel_q);
                            shard.nents -= 1;
                        } else {
                            let other_prio = list_ent_ref.prio;
                            if prio < other_prio {
                                list_ent = list_ent_ref.link.next;
                                bucket.unlink_item(list_ent_, true);
                                // only at this point, after unlink, do we know that nothing else
                                // is referencing the node
                                let list_ent_mut = unsafe { &mut *list_ent_.get() };
                                list_ent_mut.work_item_link.cancel(cancel_q);
                                shard.nents -= 1;
                            } else if prio == other_prio {
                                panic!("reader with same priority, even though we checked?");
                            } else {
                                list_ent = list_ent_ref.link.next;
                            }
                        }
                    }
                }
            }
        } else {
            // is a reader

            // a reader is okay as long as there isn't a writer
            // with a higher or *equal* priority

            let mut list_ent: Option<&UnsafeCell<StroadNode<'_, '_, P>>> = bucket.holds_lock.next;
            while let Some(list_ent_) = list_ent {
                // safety: see above
                let list_ent_ref = unsafe { &*list_ent_.get() };
                if list_ent_ref.key == key {
                    if list_ent_ref.prio < 0 {
                        let other_prio = -(list_ent_ref.prio + 1);

                        if prio < other_prio {
                            list_ent = list_ent_ref.link.next;
                        } else {
                            lock_okay = false;
                            break;
                        }
                    } else {
                        list_ent = list_ent_ref.link.next;
                    }
                }
            }
        }

        if lock_okay {
            mark_item();
        }
        let ret = shard.insert(stroad_node, hash, lock_okay);
        (lock_okay, ret)
    }

    /// For an ordered algorithm, wake everything that would be able to run
    ///
    /// Should only be called if stroad_node is holding a write lock,
    /// or if the stroad_node is holding the *last* read lock, with no write lock
    /// of lower priority pending.
    pub fn ordered_do_unlocking<VAL, UNMARK, Q: WorkQueueInterface<WorkItemTy = P::WorkItemTy>>(
        &self,
        stroad_node: &'stroad_node StroadNode<'stroad_node, 'arena, P>,
        unpark_validation: VAL,
        unmark_item: UNMARK,
        unpark_q: &mut Q,
    ) -> &'stroad_node mut StroadNode<'stroad_node, 'arena, P>
    where
        VAL: FnOnce() -> bool,
        UNMARK: FnOnce(),
    {
        let key = stroad_node.key;
        let mut prio = stroad_node.prio;

        let hash = hash(key);
        let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
        let mut shard = self.lock_shard(shard as usize);
        // shard lock held now, so we can get the bucket
        // fixme layering?
        let bucket_i = (hash >> HASH_NUM_SHARDS_SHIFT) & ((1 << shard.capacity_shift) - 1);
        let buckets_ptr_usz = shard.buckets_and_lock.load(Ordering::Relaxed) & !1;
        let buckets_ptr = buckets_ptr_usz as *mut StroadBucket<'stroad_node, 'arena, P>;
        let bucket = unsafe {
            // safety: this is the size of the buckets array
            // (which this shard exclusively owns)
            let buckets = &mut *slice_from_raw_parts_mut(buckets_ptr, 1 << shard.capacity_shift);
            &mut buckets[bucket_i as usize]
        };

        // validation for unlocking reader, with lock held
        if !unpark_validation() {
            // don't unpark anything, just unlink ourselves
            let stroad_node = to_unsafecell(stroad_node);
            bucket.unlink_item(stroad_node, true);
            unmark_item();
            return unsafe { &mut *stroad_node.get() };
        }

        // go through awaking everything that needs to be awaked
        if prio < 0 {
            // is a writer
            prio = -(prio + 1);
        } else {
            // is a reader
        }

        let mut highest_found_writer_prio: Option<i64> = None;
        let mut highest_found_writer = None;

        let mut list_ent: Option<&UnsafeCell<StroadNode<'_, '_, P>>> = bucket.wants_lock.next;
        while let Some(list_ent_) = list_ent {
            // safety: see above
            let list_ent_ref = unsafe { &*list_ent_.get() };
            if list_ent_ref.key == key {
                if list_ent_ref.prio < 0 {
                    let other_prio = -(list_ent_ref.prio + 1);

                    if other_prio < prio {
                        panic!("a writer with higher priority than us is waiting, this should not happen!");
                    } else {
                        if let Some(highest_found_writer_prio_) = highest_found_writer_prio {
                            if other_prio < highest_found_writer_prio_ {
                                highest_found_writer_prio = Some(other_prio);
                                highest_found_writer = Some(list_ent_);
                            }
                        } else {
                            highest_found_writer_prio = Some(other_prio);
                            highest_found_writer = Some(list_ent_);
                        }
                    }
                } else {
                    let other_prio = list_ent_ref.prio;

                    if other_prio < prio {
                        panic!("a reader with higher priority than us is waiting, this should not happen!");
                    }
                }

                list_ent = list_ent_ref.link.next;
            }
        }

        let mut found_readers_of_same_priority = false;

        // loop again, unparking readers as necessary
        let reader_unpark_prio = highest_found_writer_prio.unwrap_or(i64::MAX);
        let mut list_ent: Option<&UnsafeCell<StroadNode<'_, '_, P>>> = bucket.wants_lock.next;
        while let Some(list_ent_) = list_ent {
            // safety: see above
            let list_ent_ref = unsafe { &*list_ent_.get() };
            if list_ent_ref.key == key {
                if list_ent_ref.prio >= 0 {
                    let other_prio = list_ent_ref.prio;

                    if other_prio <= reader_unpark_prio {
                        if other_prio == reader_unpark_prio {
                            found_readers_of_same_priority = true;
                        }

                        list_ent = list_ent_ref.link.next;
                        bucket.unlink_item(list_ent_, false);
                        // only at this point, after unlink, do we know that nothing else
                        // is referencing the node
                        let list_ent_mut = unsafe { &mut *list_ent_.get() };
                        list_ent_mut.work_item_link.unpark(unpark_q);
                        shard.nents -= 1;
                    } else {
                        list_ent = list_ent_ref.link.next;
                    }
                } else {
                    list_ent = list_ent_ref.link.next;
                }
            }
        }

        if !found_readers_of_same_priority {
            if let Some(highest_found_writer) = highest_found_writer {
                bucket.unlink_item(highest_found_writer, false);
                let highest_found_writer_node = unsafe { &mut *highest_found_writer.get() };
                highest_found_writer_node.work_item_link.unpark(unpark_q);
                shard.nents -= 1;
            }
        }

        let stroad_node = to_unsafecell(stroad_node);
        bucket.unlink_item(stroad_node, true);
        unmark_item();
        unsafe { &mut *stroad_node.get() }
    }
}

#[cfg(test)]
mod tests;

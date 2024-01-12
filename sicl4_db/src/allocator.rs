//! Custom slab-based memory allocator
//!
//! This is a custom concurrent slab memory allocator inspired by the
//! [sharded_slab](https://docs.rs/sharded-slab/latest/sharded_slab/implementation/index.html)
//! crate, which is in turn inspired by the
//! [Mimalloc](https://www.microsoft.com/en-us/research/uploads/prod/2019/06/mimalloc-tr-v1.pdf)
//! allocator from Microsoft Research.
//!
//! There are a number of relatively-minor changes made relative to the
//! `sharded_slab` crate, but the most significant change is that the code
//! here has tighter integration between memory allocation and object locking.
//! Some notes as to why have been written
//! [here](https://arcanenibble.github.io/drafts/parallel-capable-netlist-data-structures-part-2.html)
//! (TODO CHANGE THIS WHEN PUBLISHED).

#[derive(Debug)]
pub struct SlabAlloc {}

#[cfg(test)]
mod tests {
    fn assert_send<T: Send>() {}
    fn assert_sync<T: Send>() {}

    use super::*;

    #[test]
    fn ensure_slab_alloc_send_sync() {
        assert_send::<SlabAlloc>();
        assert_sync::<SlabAlloc>();
    }
}

//! Code for controlling the running of algorithms against netlists

use std::marker::PhantomData;

// TODO
pub struct WorkItem<'arena, 'work_item> {
    _pd: PhantomData<(&'arena (), &'work_item ())>,
}

/// Abstraction over ordered/unordered work queues
pub trait WorkQueueInterface {
    type WorkItemTy;
    fn add_work(&mut self, work_item: Self::WorkItemTy);
}

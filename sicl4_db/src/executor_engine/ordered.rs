//! This module contains code to support operations where the order *does* matter.
//!
//! In other words, the "fringe" of the graph algorithm is a priority queue.

use std::marker::PhantomData;

use super::*;

pub trait OrderedAlgorithm: Send + Sync {
    type ROtoRWTy;

    fn try_process_readonly<'algo_global_state, 'view, 'arena>(
        &'algo_global_state self,
        view: &'view mut OrderedAlgorithmROView<'arena>,
        work_item: &'arena WorkItem<'arena, 'arena>,
    ) -> Result<Self::ROtoRWTy, ()>;

    fn process_finish_readwrite<'algo_state, 'view, 'arena, 'q>(
        &'algo_state self,
        view: &'view mut OrderedAlgorithmRWView<'arena, 'q>,
        work_item: &'arena WorkItem<'arena, 'arena>,
        ro_output: Self::ROtoRWTy,
    );
}

#[derive(Debug)]
pub struct OrderedAlgorithmROView<'arena> {
    _pd: PhantomData<&'arena ()>,
}

#[derive(Debug)]
pub struct OrderedAlgorithmRWView<'arena, 'q> {
    _pd: PhantomData<&'q &'arena ()>,
}

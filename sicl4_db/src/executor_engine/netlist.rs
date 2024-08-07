use std::{
    alloc::Layout,
    ops::{Deref, DerefMut},
};

use crate::{
    allocator::{TypeMappable, TypeMapper},
    lock_ops::{LockedObj, ObjRef, TypeErasedObjRef},
    netlist::{NetlistCell, NetlistCellRef, NetlistGuard, NetlistWire, NetlistWireRef},
};

use super::WorkItem;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
/// Generic type of reference to netlist nodes
pub enum NetlistRef<'arena> {
    Cell(NetlistCellRef<'arena>),
    Wire(NetlistWireRef<'arena>),
}
impl<'arena> From<NetlistCellRef<'arena>> for NetlistRef<'arena> {
    fn from(value: NetlistCellRef<'arena>) -> Self {
        Self::Cell(value)
    }
}
impl<'arena> From<NetlistWireRef<'arena>> for NetlistRef<'arena> {
    fn from(value: NetlistWireRef<'arena>) -> Self {
        Self::Wire(value)
    }
}
impl<'arena> NetlistRef<'arena> {
    pub fn cell(self) -> NetlistCellRef<'arena> {
        match self {
            NetlistRef::Cell(x) => x,
            _ => panic!("Not a Cell"),
        }
    }
    pub fn wire(self) -> NetlistWireRef<'arena> {
        match self {
            NetlistRef::Wire(x) => x,
            _ => panic!("Not a Wire"),
        }
    }

    fn type_erase(self) -> TypeErasedObjRef<'arena> {
        match self {
            NetlistRef::Cell(x) => x.type_erase(),
            NetlistRef::Wire(x) => x.type_erase(),
        }
    }
}

/// Allows read-only access to something in the netlist
#[derive(Debug)]
pub struct ROGuard<'arena, T> {
    pub x: ObjRef<'arena, T>,
}
impl<'arena, T> NetlistGuard<'arena, T> for ROGuard<'arena, T> {
    fn ref_<'guard>(&'guard self) -> ObjRef<'arena, T> {
        self.x
    }
}
impl<'arena, T> Deref for ROGuard<'arena, T> {
    type Target = T;

    fn deref(&self) -> &T {
        // safety: atomic ops (in lock_ops) ensures that there is no conflict
        unsafe { &*self.x.ptr.payload.get() }
    }
}

/// Allows read-write access (including delete) to something in the netlist
#[derive(Debug)]
pub struct RWGuard<'arena, T> {
    pub x: ObjRef<'arena, T>,
    _lock_idx: usize,
}
impl<'arena, T> NetlistGuard<'arena, T> for RWGuard<'arena, T> {
    fn ref_<'guard>(&'guard self) -> ObjRef<'arena, T> {
        self.x
    }
}
impl<'arena, T> Deref for RWGuard<'arena, T> {
    type Target = T;

    fn deref(&self) -> &T {
        // safety: atomic ops (in lock_ops) ensures that there is no conflict
        unsafe { &*self.x.ptr.payload.get() }
    }
}
impl<'arena, T> DerefMut for RWGuard<'arena, T> {
    fn deref_mut(&mut self) -> &mut T {
        // safety: atomic ops (in lock_ops) ensures that there is no conflict
        unsafe { &mut *self.x.ptr.payload.get() }
    }
}

/// Separate cells/wires/work items into separate type bins
struct NetlistTypeMapper {}
impl TypeMapper for NetlistTypeMapper {
    type BinsArrayTy<T> = [T; 3];
    const LAYOUTS: &'static [&'static [Layout]] = &[
        &[Layout::new::<LockedObj<NetlistCell>>()],
        &[Layout::new::<LockedObj<NetlistWire>>()],
        &[Layout::new::<WorkItem>()],
    ];
}
unsafe impl<'arena> TypeMappable<NetlistTypeMapper> for LockedObj<NetlistCell<'arena>> {
    const I: usize = 0;
}
unsafe impl<'arena> TypeMappable<NetlistTypeMapper> for LockedObj<NetlistWire<'arena>> {
    const I: usize = 1;
}
unsafe impl<'arena, 'work_item> TypeMappable<NetlistTypeMapper> for WorkItem<'arena, 'work_item> {
    const I: usize = 2;
}

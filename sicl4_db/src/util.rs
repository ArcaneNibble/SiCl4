use std::{
    cell::UnsafeCell,
    fmt::{self, Debug, Write},
};

/// Convert `&T` to `&UnsafeCell<T>`
pub fn to_unsafecell<T>(ptr: &T) -> &UnsafeCell<T> {
    let t = ptr as *const T as *const UnsafeCell<T>;
    // SAFETY: `T` and `UnsafeCell<T>` have the same memory layout
    unsafe { &*t }
}

// FIXME this is all hardcoded and terrible
// (and aarch64 value is designed for M1)
#[cfg(target_arch = "x86_64")]
#[macro_export]
macro_rules! align_to_cache {
    ($x:item) => {
        #[repr(align(64))]
        $x
    };
}
#[cfg(target_arch = "aarch64")]
#[macro_export]
macro_rules! align_to_cache {
    ($x:item) => {
        #[repr(align(128))]
        $x
    };
}

/// Divide, rounding up
pub const fn divroundup(num: usize, divisor: usize) -> usize {
    (num + divisor - 1) / divisor
}

/// Round to multiple
pub const fn roundto(num: usize, multiple: usize) -> usize {
    divroundup(num, multiple) * multiple
}

pub unsafe fn _debug_hexdump(p: *const u8, mut sz: usize) -> Result<String, fmt::Error> {
    let mut s = String::new();
    let mut off = 0;

    while sz > 0 {
        write!(&mut s, "{:08X}: ", off)?;
        let chunk_sz = if sz >= 16 { 16 } else { sz };
        // hex
        for i in 0..chunk_sz {
            let c = *(p.offset((off + i) as isize));
            write!(&mut s, "{:02X} ", c)?;
        }
        for _ in chunk_sz..16 {
            write!(&mut s, "   ")?;
        }
        // bar
        write!(&mut s, "| ")?;
        // ascii
        for i in 0..chunk_sz {
            let c = *(p.offset((off + i) as isize));
            if c.is_ascii_graphic() {
                write!(&mut s, "{}", c as char)?;
            } else {
                write!(&mut s, ".")?;
            }
        }
        write!(&mut s, "\n")?;
        off += chunk_sz;
        sz -= chunk_sz;
    }

    Ok(s)
}

pub struct UsizePtr(pub usize);
impl Debug for UsizePtr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "0x{:016x}", self.0)
    }
}
impl From<usize> for UsizePtr {
    fn from(value: usize) -> Self {
        Self(value)
    }
}
impl<T> From<*const T> for UsizePtr {
    fn from(value: *const T) -> Self {
        Self(value as usize)
    }
}
impl<T> From<*mut T> for UsizePtr {
    fn from(value: *mut T) -> Self {
        Self(value as usize)
    }
}
impl<T> From<&T> for UsizePtr {
    fn from(value: &T) -> Self {
        Self(value as *const T as usize)
    }
}
impl<T> From<&mut T> for UsizePtr {
    fn from(value: &mut T) -> Self {
        Self(value as *const T as usize)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn divroundup_test() {
        assert_eq!(divroundup(0, 4), 0);
        assert_eq!(divroundup(4, 4), 1);
        assert_eq!(divroundup(5, 4), 2);
    }

    #[test]
    fn roundto_test() {
        assert_eq!(roundto(0, 4), 0);
        assert_eq!(roundto(4, 4), 4);
        assert_eq!(roundto(5, 4), 8);
    }

    #[test]
    fn hexdump_test() {
        let buf = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
        let s = unsafe { _debug_hexdump(buf.as_ptr(), buf.len()).unwrap() };
        print!("{}", s);
        assert_eq!(
            s,
            "00000000: 00 01 02 03 04 05 06 07 08 09 0A 0B 0C 0D 0E 0F | ................\n"
        );

        let buf = [0x30, 0x31, 0x32, 0x33, 0x34];
        let s = unsafe { _debug_hexdump(buf.as_ptr(), buf.len()).unwrap() };
        print!("{}", s);
        assert_eq!(
            s,
            "00000000: 30 31 32 33 34                                  | 01234\n"
        );

        let buf = [
            0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3a, 0x3b, 0x3c, 0x3d,
            0x3e, 0x3f, 0x40,
        ];
        let s = unsafe { _debug_hexdump(buf.as_ptr(), buf.len()).unwrap() };
        print!("{}", s);
        assert_eq!(
            s,
            "00000000: 30 31 32 33 34 35 36 37 38 39 3A 3B 3C 3D 3E 3F | 0123456789:;<=>?\n00000010: 40                                              | @\n"
        );
    }
}

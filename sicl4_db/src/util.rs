use std::{fmt, fmt::Write};

/// Divide, rounding up
pub const fn divroundup(num: usize, divisor: usize) -> usize {
    (num + divisor - 1) / divisor
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

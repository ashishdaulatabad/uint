#![feature(error_in_core)]
// #![no_std]

trait ThenOr {
    fn then_or<T, B, Result>(self, fn1: T, fn2: B) -> Result
    where
        T: Fn() -> Result,
        B: Fn() -> Result;

    fn then_val<Result>(
        self,
        true_value: Result,
        false_value: Result,
    ) -> Result;
}

/// Count total bits in a number
///
/// ```
/// use uint::count_bits;
///
/// assert_eq!(count_bits(10), 2);    // 0x0A
/// assert_eq!(count_bits(15), 4);    // 0x0F
/// assert_eq!(count_bits(255), 8);    // 0xFF
/// assert_eq!(count_bits(0xFFFF_FFFF_FFFF_FFFF), 64);
/// assert_eq!(count_bits(0xFFFF_FFFF_FFFF_FFFF), 64);
/// ```
pub const fn count_bits(number: u64) -> u64 {
    let mut ans = (number & 0x5555_5555_5555_5555)
        + ((number & 0xAAAA_AAAA_AAAA_AAAA) >> 1);
    ans = (ans & 0x3333_3333_3333_3333) + ((ans & 0xCCCC_CCCC_CCCC_CCCC) >> 2);
    ans = (ans & 0x0F0F_0F0F_0F0F_0F0F) + ((ans & 0xF0F0_F0F0_F0F0_F0F0) >> 4);
    ans = (ans & 0x00FF_00FF_00FF_00FF) + ((ans & 0xFF00_FF00_FF00_FF00) >> 8);
    ans = (ans & 0x0000_FFFF_0000_FFFF) + ((ans & 0xFFFF_0000_FFFF_0000) >> 16);
    ans = (ans & 0x0000_0000_FFFF_FFFF) + ((ans & 0xFFFF_FFFF_0000_0000) >> 32);

    ans
}

pub mod u256;
pub mod u512;

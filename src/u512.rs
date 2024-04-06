use super::{count_bits, ParseUintError, ThenOr};

/// An extended 64-byte (or 512-bit) unsigned integer
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct U512([u64; 8]);

impl core::fmt::Display for U512 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = self
            .display_values()
            .iter()
            .enumerate()
            .rev()
            .map(|(index, c)| if index > 0 { format!("{}", c) } else { format!("{:019}", c) })
            .collect::<Vec<String>>()
            .join("");
        f.write_fmt(format_args!("{}", s))
    }
}

impl core::fmt::LowerHex for U512 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.0[0] > 0 {
            f.write_fmt(format_args!(
                "0x{:x}{:016x}{:016x}{:016x}{:016x}{:016x}{:016x}{:016x}",
                self.0[0],
                self.0[1],
                self.0[2],
                self.0[3],
                self.0[4],
                self.0[5],
                self.0[6],
                self.0[7]
            ))
        } else if self.0[1] > 0 {
            f.write_fmt(format_args!(
                "0x{:x}{:016x}{:016x}{:016x}{:016x}{:016x}{:016x}",
                self.0[1],
                self.0[2],
                self.0[3],
                self.0[4],
                self.0[5],
                self.0[6],
                self.0[7]
            ))
        } else if self.0[2] > 0 {
            f.write_fmt(format_args!(
                "0x{:x}{:016x}{:016x}{:016x}{:016x}{:016x}",
                self.0[2],
                self.0[3],
                self.0[4],
                self.0[5],
                self.0[6],
                self.0[7]
            ))
        } else if self.0[3] > 0 {
            f.write_fmt(format_args!(
                "0x{:x}{:016x}{:016x}{:016x}{:016x}",
                self.0[3], self.0[4], self.0[5], self.0[6], self.0[7]
            ))
        } else if self.0[4] > 0 {
            f.write_fmt(format_args!(
                "0x{:x}{:016x}{:016x}{:016x}",
                self.0[4], self.0[5], self.0[6], self.0[7]
            ))
        } else if self.0[5] > 0 {
            f.write_fmt(format_args!(
                "0x{:x}{:016x}{:016x}",
                self.0[5], self.0[6], self.0[7]
            ))
        } else if self.0[6] > 0 {
            f.write_fmt(format_args!("0x{:x}{:016x}", self.0[6], self.0[7]))
        } else {
            f.write_fmt(format_args!("0x{:x}", self.0[7]))
        }
    }
}

impl core::fmt::UpperHex for U512 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.0[0] > 0 {
            f.write_fmt(format_args!(
                "0x{:X}{:016X}{:016X}{:016X}{:016X}{:016X}{:016X}{:016X}",
                self.0[0],
                self.0[1],
                self.0[2],
                self.0[3],
                self.0[4],
                self.0[5],
                self.0[6],
                self.0[7]
            ))
        } else if self.0[1] > 0 {
            f.write_fmt(format_args!(
                "0x{:X}{:016X}{:016X}{:016X}{:016X}{:016X}{:016X}",
                self.0[1],
                self.0[2],
                self.0[3],
                self.0[4],
                self.0[5],
                self.0[6],
                self.0[7]
            ))
        } else if self.0[2] > 0 {
            f.write_fmt(format_args!(
                "0x{:X}{:016X}{:016X}{:016X}{:016X}{:016X}",
                self.0[2],
                self.0[3],
                self.0[4],
                self.0[5],
                self.0[6],
                self.0[7]
            ))
        } else if self.0[3] > 0 {
            f.write_fmt(format_args!(
                "0x{:X}{:016X}{:016X}{:016X}{:016X}",
                self.0[3], self.0[4], self.0[5], self.0[6], self.0[7]
            ))
        } else if self.0[4] > 0 {
            f.write_fmt(format_args!(
                "0x{:X}{:016X}{:016X}{:016X}",
                self.0[4], self.0[5], self.0[6], self.0[7]
            ))
        } else if self.0[5] > 0 {
            f.write_fmt(format_args!(
                "0x{:X}{:016X}{:016X}",
                self.0[5], self.0[6], self.0[7]
            ))
        } else if self.0[6] > 0 {
            f.write_fmt(format_args!("0x{:X}{:016X}", self.0[6], self.0[7]))
        } else {
            f.write_fmt(format_args!("0x{:X}", self.0[7]))
        }
    }
}

impl U512 {
    /// Maximum value for `U512`
    pub const MAX: Self = U512([0xFFFF_FFFF_FFFF_FFFF; 8]);

    /// Minimum possible value for `U512`
    pub const MIN: Self = U512([0; 8]);

    /// Minimum possible value for `U512`
    pub const ZERO: Self = U512([0; 8]);

    /// Constant Value: 1 for `U512`
    pub const ONE: Self = U512([0, 0, 0, 0, 0, 0, 0, 1]);

    /// Create new from Raw value
    #[inline(always)]
    pub const fn raw(value: [u64; 8]) -> Self {
        Self(value)
    }

    #[inline(always)]
    pub const fn raw_eq(self, other: [u64; 8]) -> bool {
        self.0[0] == other[0]
            && self.0[1] == other[1]
            && self.0[2] == other[2]
            && self.0[3] == other[3]
            && self.0[4] == other[4]
            && self.0[5] == other[5]
            && self.0[6] == other[6]
            && self.0[7] == other[7]
    }

    /// Create new value from string number
    /// # Error
    /// Returns `ParseUintError` if invalid number is found
    ///
    /// ### Example
    /// ```
    /// use uint::u512::U512;
    ///
    /// let p = U512::from_string("12");
    /// assert!(p.is_ok_and(|c| c.raw_eq([0, 0, 0, 0, 0, 0, 0, 12])));
    /// let p = U512::from_string("12312");
    /// assert!(p.is_ok_and(|c| c.raw_eq([0, 0, 0, 0, 0, 0, 0, 12312])));
    /// let p = U512::from_string("12312aa");
    /// assert!(p.is_err());
    /// ```
    pub fn from_string(string: &str) -> Result<Self, ParseUintError> {
        let mut value = U512::ZERO;

        for chr in string.chars().filter(|c| *c != '_') {
            let digit = chr.to_digit(10);

            if let Some(dig) = digit {
                let (value_x_8, value_x_2) = (value << 3, value << 1);
                value = (value_x_8 + value_x_2).add_single(dig as u64);
            } else {
                return Err(ParseUintError::InvalidDigit);
            }
        }

        Ok(value)
    }

    #[inline]
    fn check_radixes(string: &str, radix: u32) -> bool {
        match radix {
            2 => string.starts_with("0b"),
            8 => string.starts_with("0o"),
            16 => string.starts_with("0x"),
            _ => false,
        }
    }

    /// Create new value from string number, returns
    /// # Error
    /// Returns ParseUintError if invalid number is found
    ///
    /// ### Example
    /// ```
    /// use uint::u512::U512;
    ///
    /// let p = U512::from_string_radix_pow_2("0x12", 16);
    /// assert!(p.is_ok_and(|x| x.raw_eq([0, 0, 0, 0, 0, 0, 0, 0x12])));
    /// let p = U512::from_string_radix_pow_2("0o12312", 8);
    /// assert!(p.is_ok_and(|x| x.raw_eq([0, 0, 0, 0, 0, 0, 0, 0o12312])));
    /// let p = U512::from_string_radix_pow_2("0b11110011", 2);
    /// assert!(p.is_ok_and(|x| x.raw_eq([0, 0, 0, 0, 0, 0, 0, 0b11110011])));
    /// ```
    pub fn from_string_radix_pow_2(
        string: &str,
        radix: u32,
    ) -> Result<Self, ParseUintError> {
        let mut value = U512::ZERO;

        let skip = if Self::check_radixes(string, radix) {
            2
        } else {
            0
        };
        let pow = match radix {
            2 => 1,
            8 => 3,
            16 => 4,
            _ => return Err(ParseUintError::InvalidRadix),
        };

        for chr in string.chars().skip(skip).filter(|c| *c != '_') {
            let digit = chr.to_digit(radix);

            if let Some(dig) = digit {
                let value_raised_pow = value << pow;
                value = value_raised_pow ^ (dig as u64);
            } else {
                return Err(ParseUintError::InvalidDigit);
            }
        }

        Ok(value)
    }

    fn add_internal(self, other: Self) -> Self {
        let mut arr = [0; 8];

        arr[7] = self.0[7].wrapping_add(other.0[7]);
        arr[6] = self.0[6].wrapping_add(other.0[6]);
        arr[5] = self.0[5].wrapping_add(other.0[5]);
        arr[4] = self.0[4].wrapping_add(other.0[4]);
        arr[3] = self.0[3].wrapping_add(other.0[3]);
        arr[2] = self.0[2].wrapping_add(other.0[2]);
        arr[1] = self.0[1].wrapping_add(other.0[1]);
        arr[0] = self.0[0].wrapping_add(other.0[0]);

        let (
            arr6_temp,
            arr5_temp,
            arr4_temp,
            arr3_temp,
            arr2_temp,
            arr1_temp,
            arr0_temp,
        ) = (
            arr[6].wrapping_add((arr[7] < self.0[7]).then_val(1, 0)),
            arr[5].wrapping_add((arr[6] < self.0[6]).then_val(1, 0)),
            arr[4].wrapping_add((arr[5] < self.0[5]).then_val(1, 0)),
            arr[3].wrapping_add((arr[4] < self.0[4]).then_val(1, 0)),
            arr[2].wrapping_add((arr[3] < self.0[3]).then_val(1, 0)),
            arr[1].wrapping_add((arr[2] < self.0[2]).then_val(1, 0)),
            arr[0].wrapping_add((arr[1] < self.0[1]).then_val(1, 0)),
        );

        let (
            carry_add5,
            carry_add4,
            carry_add3,
            carry_add2,
            carry_add1,
            carry_add0,
        ) = (
            arr5_temp.wrapping_add((arr6_temp < arr[6]).then_val(1, 0)),
            arr4_temp.wrapping_add((arr5_temp < arr[5]).then_val(1, 0)),
            arr3_temp.wrapping_add((arr4_temp < arr[4]).then_val(1, 0)),
            arr2_temp.wrapping_add((arr3_temp < arr[3]).then_val(1, 0)),
            arr1_temp.wrapping_add((arr2_temp < arr[2]).then_val(1, 0)),
            arr0_temp.wrapping_add((arr1_temp < arr[1]).then_val(1, 0)),
        );

        let (acarry_add4, acarry_add3, acarry_add2, acarry_add1, acarry_add0) = (
            carry_add4.wrapping_add((carry_add5 < arr5_temp).then_val(1, 0)),
            carry_add3.wrapping_add((carry_add4 < arr4_temp).then_val(1, 0)),
            carry_add2.wrapping_add((carry_add3 < arr3_temp).then_val(1, 0)),
            carry_add1.wrapping_add((carry_add2 < arr2_temp).then_val(1, 0)),
            carry_add0.wrapping_add((carry_add1 < arr1_temp).then_val(1, 0)),
        );

        let (an_carry_add3, an_carry_add2, an_carry_add1, an_carry_add0) = (
            acarry_add3.wrapping_add((acarry_add4 < carry_add4).then_val(1, 0)),
            acarry_add2.wrapping_add((acarry_add3 < carry_add3).then_val(1, 0)),
            acarry_add1.wrapping_add((acarry_add2 < carry_add2).then_val(1, 0)),
            acarry_add0.wrapping_add((acarry_add1 < carry_add1).then_val(1, 0)),
        );

        let (ano_carry_add2, ano_carry_add1, ano_carry_add0) = (
            an_carry_add2
                .wrapping_add((an_carry_add3 < acarry_add3).then_val(1, 0)),
            an_carry_add1
                .wrapping_add((an_carry_add2 < acarry_add2).then_val(1, 0)),
            an_carry_add0
                .wrapping_add((an_carry_add1 < acarry_add1).then_val(1, 0)),
        );

        let (anof_carry_add1, anof_carry_add0) = (
            ano_carry_add1
                .wrapping_add((ano_carry_add2 < an_carry_add2).then_val(1, 0)),
            ano_carry_add0
                .wrapping_add((ano_carry_add1 < an_carry_add1).then_val(1, 0)),
        );

        let final_0 = anof_carry_add0
            .wrapping_add((anof_carry_add1 < ano_carry_add1).then_val(1, 0));
        (arr[6], arr[5], arr[4], arr[3], arr[2], arr[1], arr[0]) = (
            arr6_temp,
            carry_add5,
            acarry_add4,
            an_carry_add3,
            ano_carry_add2,
            anof_carry_add1,
            final_0,
        );

        Self(arr)
    }

    #[inline(always)]
    fn add_single(self, other: u64) -> Self {
        let mut p = self.0;
        p[7] = self.0[7].wrapping_add(other);
        p[6] = self.0[6].wrapping_add((p[7] < self.0[7]).then_val(1, 0));
        p[5] = self.0[5].wrapping_add((p[6] < self.0[6]).then_val(1, 0));
        p[4] = self.0[4].wrapping_add((p[5] < self.0[5]).then_val(1, 0));
        p[3] = self.0[3].wrapping_add((p[4] < self.0[4]).then_val(1, 0));
        p[2] = self.0[2].wrapping_add((p[3] < self.0[3]).then_val(1, 0));
        p[1] = self.0[1].wrapping_add((p[2] < self.0[2]).then_val(1, 0));
        p[0] = self.0[0].wrapping_add((p[1] < self.0[1]).then_val(1, 0));

        Self(p)
    }

    #[inline]
    fn mul_single_other(self, other: u64) -> Self {
        // Multiply first half and second half
        let other_u128 = other as u128;
        let mut answer = [
            (self.0[0]) as u128,
            (self.0[1]) as u128,
            (self.0[2]) as u128,
            (self.0[3]) as u128,
            (self.0[4]) as u128,
            (self.0[5]) as u128,
            (self.0[6]) as u128,
            (self.0[7]) as u128,
        ];

        answer[7] = answer[7].wrapping_mul(other_u128);
        answer[6] = answer[6].wrapping_mul(other_u128);
        answer[5] = answer[5].wrapping_mul(other_u128);
        answer[4] = answer[4].wrapping_mul(other_u128);
        answer[3] = answer[3].wrapping_mul(other_u128);
        answer[2] = answer[2].wrapping_mul(other_u128);
        answer[1] = answer[1].wrapping_mul(other_u128);
        answer[0] = answer[0].wrapping_mul(other_u128);

        answer[6] = answer[6].wrapping_add(answer[7] >> 64);
        answer[5] = answer[5].wrapping_add(answer[6] >> 64);
        answer[4] = answer[4].wrapping_add(answer[5] >> 64);
        answer[3] = answer[3].wrapping_add(answer[4] >> 64);
        answer[2] = answer[2].wrapping_add(answer[3] >> 64);
        answer[1] = answer[1].wrapping_add(answer[2] >> 64);
        answer[0] = answer[0].wrapping_add(answer[1] >> 64);

        answer[7] &= 0xFFFF_FFFF_FFFF_FFFF;
        answer[6] &= 0xFFFF_FFFF_FFFF_FFFF;
        answer[5] &= 0xFFFF_FFFF_FFFF_FFFF;
        answer[4] &= 0xFFFF_FFFF_FFFF_FFFF;
        answer[3] &= 0xFFFF_FFFF_FFFF_FFFF;
        answer[2] &= 0xFFFF_FFFF_FFFF_FFFF;
        answer[1] &= 0xFFFF_FFFF_FFFF_FFFF;
        answer[0] &= 0xFFFF_FFFF_FFFF_FFFF;

        U512::raw(answer.map(|c| c as u64))
    }

    fn div_internal(self, other: Self) -> Self {
        match self.cmp(&other) {
            core::cmp::Ordering::Less => Self::ZERO,
            core::cmp::Ordering::Equal => Self::ONE,
            _ => {
                let div = other;
                let mut divisor = other;
                let leading_zeros = divisor.leading_zeros();
                divisor <<= leading_zeros - self.leading_zeros();

                let mut value = self;
                let mut quotient = Self::MIN;

                while value >= div {
                    while value < divisor {
                        divisor >>= 1;
                        quotient <<= 1;
                    }

                    value -= divisor;
                    quotient = quotient.add_single(1);
                }
                let rem_offset = div.leading_zeros() - divisor.leading_zeros();

                quotient << rem_offset
            }
        }
    }

    fn rem_internal(self, other: Self) -> Self {
        match self.cmp(&other) {
            core::cmp::Ordering::Less => self,
            core::cmp::Ordering::Equal => Self::ZERO,
            _ => {
                let div = other;
                let mut divisor = other;
                let leading_zeros = divisor.leading_zeros();
                divisor <<= leading_zeros - self.leading_zeros();

                let mut value = self;

                while value >= div {
                    while value < divisor {
                        divisor >>= 1;
                    }

                    value -= divisor;
                }

                value
            }
        }
    }

    fn div_rem_internal(self, other: Self) -> (Self, Self) {
        match self.cmp(&other) {
            core::cmp::Ordering::Less => (Self::ZERO, self),
            core::cmp::Ordering::Equal => (Self::ONE, Self::ZERO),
            _ => {
                let div = other;
                let mut divisor = other;
                let leading_zeros = divisor.leading_zeros();
                divisor <<= leading_zeros - self.leading_zeros();

                let mut value = self;
                let mut quotient = Self::ZERO;

                while value >= div {
                    while value < divisor {
                        divisor >>= 1;
                        quotient <<= 1;
                    }

                    value -= divisor;
                    quotient = quotient.add_single(1);
                }
                let rem_offset = div.leading_zeros() - divisor.leading_zeros();

                (quotient << rem_offset, value)
            }
        }
    }

    fn display_values(self) -> Vec<u64> {
        let divisor = Self::from(10_000_000_000_000_000_000_u64);
        let mut value = self;
        let mut values = vec![];
        loop {
            let (q, rem) = value.div_rem_internal(divisor);
            value = q;
            values.push(rem.0[7]);

            if q.is_zero() {
                break;
            }
        }

        println!("{:?}", values);
        values
    }

    pub fn div_single(self, divisor: u64) -> Self {
        let div = Self([0, 0, 0, 0, 0, 0, 0, divisor]);
        let mut div_512 = Self([0, 0, 0, 0, 0, 0, 0, divisor]);
        let leading_zeros = div_512.leading_zeros();
        div_512 <<= leading_zeros - self.leading_zeros();

        let mut value = self;
        let mut quotient = U512::ZERO;

        while value >= div {
            while value < div_512 {
                div_512 >>= 1;
                quotient <<= 1;
            }

            value -= div_512;
            quotient = quotient.add_single(1);
        }
        let rem_offset = div.leading_zeros() - div_512.leading_zeros();

        quotient << rem_offset
    }

    pub fn rem_single(self, divisor: u64) -> Self {
        let div = Self([0, 0, 0, 0, 0, 0, 0, divisor]);
        let mut div_512 = Self([0, 0, 0, 0, 0, 0, 0, divisor]);
        let leading_zeros = div_512.leading_zeros();
        div_512 <<= leading_zeros - self.leading_zeros();

        let mut value = self;
        let mut quotient = U512::ZERO;

        while value >= div {
            while value < div_512 {
                div_512 >>= 1;
                quotient <<= 1;
            }

            value -= div_512;
            quotient = quotient.add_single(1);
        }

        value
    }

    #[inline]
    fn mul_internal(self, other: U512) -> Self {
        // Multiply first half and second half
        let first = self.mul_single_other(other.0[7]);
        let second = self.mul_single_other(other.0[6]);
        let third = self.mul_single_other(other.0[5]);
        let fourth = self.mul_single_other(other.0[4]);

        let fifth = self.mul_single_other(other.0[3]);
        let sixth = self.mul_single_other(other.0[2]);
        let seventh = self.mul_single_other(other.0[1]);
        let eighth = self.mul_single_other(other.0[0]);

        (first)
            + (second << 64)
            + (third << 128)
            + (fourth << 192)
            + (fifth << 256)
            + (sixth << 320)
            + (seventh << 384)
            + (eighth << 448)
    }

    pub fn sub_internal(self, other: Self) -> Self {
        let mut arr = [0; 8];

        arr[7] = self.0[7].wrapping_sub(other.0[7]);
        arr[6] = self.0[6].wrapping_sub(other.0[6]);
        arr[5] = self.0[5].wrapping_sub(other.0[5]);
        arr[4] = self.0[4].wrapping_sub(other.0[4]);
        arr[3] = self.0[3].wrapping_sub(other.0[3]);
        arr[2] = self.0[2].wrapping_sub(other.0[2]);
        arr[1] = self.0[1].wrapping_sub(other.0[1]);
        arr[0] = self.0[0].wrapping_sub(other.0[0]);

        let (
            arr6_temp,
            arr5_temp,
            arr4_temp,
            arr3_temp,
            arr2_temp,
            arr1_temp,
            arr0_temp,
        ) = (
            arr[6].wrapping_sub((arr[7] > self.0[7]).then_val(1, 0)),
            arr[5].wrapping_sub((arr[6] > self.0[6]).then_val(1, 0)),
            arr[4].wrapping_sub((arr[5] > self.0[5]).then_val(1, 0)),
            arr[3].wrapping_sub((arr[4] > self.0[4]).then_val(1, 0)),
            arr[2].wrapping_sub((arr[3] > self.0[3]).then_val(1, 0)),
            arr[1].wrapping_sub((arr[2] > self.0[2]).then_val(1, 0)),
            arr[0].wrapping_sub((arr[1] > self.0[1]).then_val(1, 0)),
        );

        let (
            carry_add5,
            carry_add4,
            carry_add3,
            carry_add2,
            carry_add1,
            carry_add0,
        ) = (
            arr5_temp.wrapping_sub((arr6_temp > arr[6]).then_val(1, 0)),
            arr4_temp.wrapping_sub((arr5_temp > arr[5]).then_val(1, 0)),
            arr3_temp.wrapping_sub((arr4_temp > arr[4]).then_val(1, 0)),
            arr2_temp.wrapping_sub((arr3_temp > arr[3]).then_val(1, 0)),
            arr1_temp.wrapping_sub((arr2_temp > arr[2]).then_val(1, 0)),
            arr0_temp.wrapping_sub((arr1_temp > arr[1]).then_val(1, 0)),
        );

        let (acarry_add4, acarry_add3, acarry_add2, acarry_add1, acarry_add0) = (
            carry_add4.wrapping_sub((carry_add5 > arr5_temp).then_val(1, 0)),
            carry_add3.wrapping_sub((carry_add4 > arr4_temp).then_val(1, 0)),
            carry_add2.wrapping_sub((carry_add3 > arr3_temp).then_val(1, 0)),
            carry_add1.wrapping_sub((carry_add2 > arr2_temp).then_val(1, 0)),
            carry_add0.wrapping_sub((carry_add1 > arr1_temp).then_val(1, 0)),
        );

        let (an_carry_add3, an_carry_add2, an_carry_add1, an_carry_add0) = (
            acarry_add3.wrapping_sub((acarry_add4 > carry_add4).then_val(1, 0)),
            acarry_add2.wrapping_sub((acarry_add3 > carry_add3).then_val(1, 0)),
            acarry_add1.wrapping_sub((acarry_add2 > carry_add2).then_val(1, 0)),
            acarry_add0.wrapping_sub((acarry_add1 > carry_add1).then_val(1, 0)),
        );

        let (ano_carry_add2, ano_carry_add1, ano_carry_add0) = (
            an_carry_add2
                .wrapping_sub((an_carry_add3 > acarry_add3).then_val(1, 0)),
            an_carry_add1
                .wrapping_sub((an_carry_add2 > acarry_add2).then_val(1, 0)),
            an_carry_add0
                .wrapping_sub((an_carry_add1 > acarry_add1).then_val(1, 0)),
        );

        let (anof_carry_add1, anof_carry_add0) = (
            ano_carry_add1
                .wrapping_sub((ano_carry_add2 > an_carry_add2).then_val(1, 0)),
            ano_carry_add0
                .wrapping_sub((ano_carry_add1 > an_carry_add1).then_val(1, 0)),
        );

        let final_0 = anof_carry_add0
            .wrapping_sub((anof_carry_add1 > ano_carry_add1).then_val(1, 0));

        (arr[6], arr[5], arr[4], arr[3], arr[2], arr[1], arr[0]) = (
            arr6_temp,
            carry_add5,
            acarry_add4,
            an_carry_add3,
            ano_carry_add2,
            anof_carry_add1,
            final_0,
        );

        Self(arr)
    }

    fn shift_left_internal(self, rhs: u32) -> Self {
        let (arr_offset, shft) = (rhs >> 6, rhs & 63);
        if shft > 0 {
            match arr_offset {
                0 => Self([
                    (self.0[0].wrapping_shl(shft))
                        | (self.0[1].wrapping_shr(64 - shft)),
                    (self.0[1].wrapping_shl(shft))
                        | (self.0[2].wrapping_shr(64 - shft)),
                    (self.0[2].wrapping_shl(shft))
                        | (self.0[3].wrapping_shr(64 - shft)),
                    self.0[3].wrapping_shl(shft)
                        | (self.0[4].wrapping_shr(64 - shft)),
                    (self.0[4].wrapping_shl(shft))
                        | (self.0[5].wrapping_shr(64 - shft)),
                    (self.0[5].wrapping_shl(shft))
                        | (self.0[6].wrapping_shr(64 - shft)),
                    (self.0[6].wrapping_shl(shft))
                        | (self.0[7].wrapping_shr(64 - shft)),
                    self.0[7].wrapping_shl(shft),
                ]),
                1 => Self([
                    (self.0[1].wrapping_shl(shft))
                        | (self.0[2].wrapping_shr(64 - shft)),
                    (self.0[2].wrapping_shl(shft))
                        | (self.0[3].wrapping_shr(64 - shft)),
                    self.0[3].wrapping_shl(shft)
                        | (self.0[4].wrapping_shr(64 - shft)),
                    (self.0[4].wrapping_shl(shft))
                        | (self.0[5].wrapping_shr(64 - shft)),
                    (self.0[5].wrapping_shl(shft))
                        | (self.0[6].wrapping_shr(64 - shft)),
                    (self.0[6].wrapping_shl(shft))
                        | (self.0[7].wrapping_shr(64 - shft)),
                    self.0[7].wrapping_shl(shft),
                    0,
                ]),
                2 => Self([
                    (self.0[2].wrapping_shl(shft))
                        | (self.0[3].wrapping_shr(64 - shft)),
                    self.0[3].wrapping_shl(shft)
                        | (self.0[4].wrapping_shr(64 - shft)),
                    (self.0[4].wrapping_shl(shft))
                        | (self.0[5].wrapping_shr(64 - shft)),
                    (self.0[5].wrapping_shl(shft))
                        | (self.0[6].wrapping_shr(64 - shft)),
                    (self.0[6].wrapping_shl(shft))
                        | (self.0[7].wrapping_shr(64 - shft)),
                    self.0[7].wrapping_shl(shft),
                    0,
                    0,
                ]),
                3 => Self([
                    self.0[3].wrapping_shl(shft)
                        | (self.0[4].wrapping_shr(64 - shft)),
                    (self.0[4].wrapping_shl(shft))
                        | (self.0[5].wrapping_shr(64 - shft)),
                    (self.0[5].wrapping_shl(shft))
                        | (self.0[6].wrapping_shr(64 - shft)),
                    (self.0[6].wrapping_shl(shft))
                        | (self.0[7].wrapping_shr(64 - shft)),
                    self.0[7].wrapping_shl(shft),
                    0,
                    0,
                    0,
                ]),
                4 => Self([
                    (self.0[4].wrapping_shl(shft))
                        | (self.0[5].wrapping_shr(64 - shft)),
                    (self.0[5].wrapping_shl(shft))
                        | (self.0[6].wrapping_shr(64 - shft)),
                    (self.0[6].wrapping_shl(shft))
                        | (self.0[7].wrapping_shr(64 - shft)),
                    self.0[7].wrapping_shl(shft),
                    0,
                    0,
                    0,
                    0,
                ]),
                5 => Self([
                    (self.0[5].wrapping_shl(shft))
                        | (self.0[6].wrapping_shr(64 - shft)),
                    (self.0[6].wrapping_shl(shft))
                        | (self.0[7].wrapping_shr(64 - shft)),
                    self.0[7].wrapping_shl(shft),
                    0,
                    0,
                    0,
                    0,
                    0,
                ]),
                6 => Self([
                    (self.0[6].wrapping_shl(shft))
                        | (self.0[7].wrapping_shr(64 - shft)),
                    self.0[7].wrapping_shl(shft),
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                ]),
                7 => Self([self.0[7].wrapping_shl(shft), 0, 0, 0, 0, 0, 0, 0]),
                _ => U512::ZERO,
            }
        } else {
            match arr_offset {
                0 => self,
                1 => Self([
                    self.0[1], self.0[2], self.0[3], self.0[4], self.0[5],
                    self.0[6], self.0[7], 0,
                ]),
                2 => Self([
                    self.0[2], self.0[3], self.0[4], self.0[5], self.0[6],
                    self.0[7], 0, 0,
                ]),
                3 => Self([
                    self.0[3], self.0[4], self.0[5], self.0[6], self.0[7], 0,
                    0, 0,
                ]),
                4 => Self([
                    self.0[4], self.0[5], self.0[6], self.0[7], 0, 0, 0, 0,
                ]),
                5 => Self([self.0[5], self.0[6], self.0[7], 0, 0, 0, 0, 0]),
                6 => Self([self.0[6], self.0[7], 0, 0, 0, 0, 0, 0]),
                7 => Self([self.0[7], 0, 0, 0, 0, 0, 0, 0]),
                _ => U512::ZERO,
            }
        }
    }

    fn shift_right_internal(self, rhs: u32) -> Self {
        let (arr_offset, shft) = (rhs >> 6, rhs & 63);
        if shft > 0 {
            match arr_offset {
                0 => Self([
                    self.0[0].wrapping_shr(shft),
                    (self.0[1].wrapping_shr(shft))
                        | (self.0[0].wrapping_shl(64 - shft)),
                    (self.0[2].wrapping_shr(shft))
                        | (self.0[1].wrapping_shl(64 - shft)),
                    (self.0[3].wrapping_shr(shft))
                        | (self.0[2].wrapping_shl(64 - shft)),
                    (self.0[4].wrapping_shr(shft))
                        | (self.0[3].wrapping_shl(64 - shft)),
                    (self.0[5].wrapping_shr(shft))
                        | (self.0[4].wrapping_shl(64 - shft)),
                    (self.0[6].wrapping_shr(shft))
                        | (self.0[5].wrapping_shl(64 - shft)),
                    (self.0[7].wrapping_shr(shft))
                        | (self.0[6].wrapping_shl(64 - shft)),
                ]),
                1 => Self([
                    0,
                    self.0[0].wrapping_shr(shft),
                    (self.0[1].wrapping_shr(shft))
                        | (self.0[0].wrapping_shl(64 - shft)),
                    (self.0[2].wrapping_shr(shft))
                        | (self.0[1].wrapping_shl(64 - shft)),
                    (self.0[3].wrapping_shr(shft))
                        | (self.0[2].wrapping_shl(64 - shft)),
                    (self.0[4].wrapping_shr(shft))
                        | (self.0[3].wrapping_shl(64 - shft)),
                    (self.0[5].wrapping_shr(shft))
                        | (self.0[4].wrapping_shl(64 - shft)),
                    (self.0[6].wrapping_shr(shft))
                        | (self.0[5].wrapping_shl(64 - shft)),
                ]),
                2 => Self([
                    0,
                    0,
                    self.0[0].wrapping_shr(shft),
                    (self.0[1].wrapping_shr(shft))
                        | (self.0[0].wrapping_shl(64 - shft)),
                    (self.0[2].wrapping_shr(shft))
                        | (self.0[1].wrapping_shl(64 - shft)),
                    (self.0[3].wrapping_shr(shft))
                        | (self.0[2].wrapping_shl(64 - shft)),
                    (self.0[4].wrapping_shr(shft))
                        | (self.0[3].wrapping_shl(64 - shft)),
                    (self.0[5].wrapping_shr(shft))
                        | (self.0[4].wrapping_shl(64 - shft)),
                ]),
                3 => Self([
                    0,
                    0,
                    0,
                    self.0[0].wrapping_shr(shft),
                    (self.0[1].wrapping_shr(shft))
                        | (self.0[0].wrapping_shl(64 - shft)),
                    (self.0[2].wrapping_shr(shft))
                        | (self.0[1].wrapping_shl(64 - shft)),
                    (self.0[3].wrapping_shr(shft))
                        | (self.0[2].wrapping_shl(64 - shft)),
                    (self.0[4].wrapping_shr(shft))
                        | (self.0[3].wrapping_shl(64 - shft)),
                ]),
                4 => Self([
                    0,
                    0,
                    0,
                    0,
                    self.0[0].wrapping_shr(shft),
                    (self.0[1].wrapping_shr(shft))
                        | (self.0[0].wrapping_shl(64 - shft)),
                    (self.0[2].wrapping_shr(shft))
                        | (self.0[1].wrapping_shl(64 - shft)),
                    (self.0[3].wrapping_shr(shft))
                        | (self.0[2].wrapping_shl(64 - shft)),
                ]),
                5 => Self([
                    0,
                    0,
                    0,
                    0,
                    0,
                    self.0[0].wrapping_shr(shft),
                    (self.0[1].wrapping_shr(shft))
                        | (self.0[0].wrapping_shl(64 - shft)),
                    (self.0[2].wrapping_shr(shft))
                        | (self.0[1].wrapping_shl(64 - shft)),
                ]),
                6 => Self([
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    self.0[0].wrapping_shr(shft),
                    (self.0[1].wrapping_shr(shft))
                        | (self.0[0].wrapping_shl(64 - shft)),
                ]),
                7 => Self([0, 0, 0, 0, 0, 0, 0, self.0[0].wrapping_shr(shft)]),
                _ => U512::ZERO,
            }
        } else {
            match arr_offset {
                0 => self,
                1 => Self([
                    0, self.0[0], self.0[1], self.0[2], self.0[3], self.0[4],
                    self.0[5], self.0[6],
                ]),
                2 => Self([
                    0, 0, self.0[0], self.0[1], self.0[2], self.0[3],
                    self.0[4], self.0[5],
                ]),
                3 => Self([
                    0, 0, 0, self.0[0], self.0[1], self.0[2], self.0[3],
                    self.0[4],
                ]),
                4 => Self([
                    0, 0, 0, 0, self.0[0], self.0[1], self.0[2], self.0[3],
                ]),
                5 => Self([0, 0, 0, 0, 0, self.0[0], self.0[1], self.0[2]]),
                6 => Self([0, 0, 0, 0, 0, 0, self.0[0], self.0[1]]),
                7 => Self([0, 0, 0, 0, 0, 0, 0, self.0[0]]),
                _ => U512::ZERO,
            }
        }
    }

    /// Convenient function to check whether this number is
    /// zero or not
    ///
    /// ### Example
    /// ```
    /// use uint::u512::U512;
    ///
    /// assert!(U512::from_string("0").is_ok_and(|c| c.is_zero()));
    /// assert!(U512::from_string("1").is_ok_and(|d| !d.is_zero()));
    /// ```
    #[inline(always)]
    pub const fn is_zero(&self) -> bool {
        self.0[0] == 0
            && self.0[1] == 0
            && self.0[2] == 0
            && self.0[3] == 0
            && self.0[4] == 0
            && self.0[5] == 0
            && self.0[6] == 0
            && self.0[7] == 0
    }

    /// Convenient function to check whether this number is
    /// zero or not
    ///
    /// ### Example
    /// ```
    /// use uint::u512::U512;
    ///
    /// assert!((U512::ONE << 64).trailing_zeros() == 64);
    /// assert!((U512::ONE << 192).trailing_zeros() == 192);
    /// ```
    pub const fn trailing_zeros(&self) -> u32 {
        if self.0[7] > 0 {
            self.0[7].trailing_zeros()
        } else if self.0[6] > 0 {
            64 + self.0[6].trailing_zeros()
        } else if self.0[5] > 0 {
            128 + self.0[5].trailing_zeros()
        } else if self.0[4] > 0 {
            192 + self.0[4].trailing_zeros()
        } else if self.0[3] > 0 {
            256 + self.0[3].trailing_zeros()
        } else if self.0[2] > 0 {
            320 + self.0[2].trailing_zeros()
        } else if self.0[1] > 0 {
            384 + self.0[1].trailing_zeros()
        } else if self.0[0] > 0 {
            448 + self.0[0].trailing_zeros()
        } else {
            512
        }
    }

    /// Convenient function to check whether this number is
    /// zero or not
    ///
    /// ### Example
    /// ```
    /// use uint::u512::U512;
    ///
    /// assert!((U512::ONE << 64).leading_zeros() == 191 + 256);
    /// assert!((U512::ONE << 192).leading_zeros() == 63 + 256);
    /// ```
    pub const fn leading_zeros(&self) -> u32 {
        if self.0[0] > 0 {
            self.0[0].leading_zeros()
        } else if self.0[1] > 0 {
            64 + self.0[1].leading_zeros()
        } else if self.0[2] > 0 {
            128 + self.0[2].leading_zeros()
        } else if self.0[3] > 0 {
            192 + self.0[3].leading_zeros()
        } else if self.0[4] > 0 {
            256 + self.0[4].leading_zeros()
        } else if self.0[5] > 0 {
            320 + self.0[5].leading_zeros()
        } else if self.0[6] > 0 {
            384 + self.0[6].leading_zeros()
        } else if self.0[7] > 0 {
            448 + self.0[7].leading_zeros()
        } else {
            512
        }
    }

    #[inline(always)]
    pub const fn bits(self) -> u64 {
        count_bits(self.0[0])
            + count_bits(self.0[1])
            + count_bits(self.0[2])
            + count_bits(self.0[3])
            + count_bits(self.0[4])
            + count_bits(self.0[5])
            + count_bits(self.0[6])
            + count_bits(self.0[7])
    }
}

impl core::ops::Not for U512 {
    type Output = U512;

    #[inline(always)]
    fn not(self) -> Self::Output {
        Self([
            !self.0[0], !self.0[1], !self.0[2], !self.0[3], !self.0[4],
            !self.0[5], !self.0[6], !self.0[7],
        ])
    }
}

impl core::cmp::Ord for U512 {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        if self.0[0] != other.0[0] {
            return self.0[0].cmp(&other.0[0]);
        }
        if self.0[1] != other.0[1] {
            return self.0[1].cmp(&other.0[1]);
        }
        if self.0[2] != other.0[2] {
            return self.0[2].cmp(&other.0[2]);
        }
        if self.0[3] != other.0[3] {
            return self.0[3].cmp(&other.0[3]);
        }
        if self.0[4] != other.0[4] {
            return self.0[4].cmp(&other.0[4]);
        }
        if self.0[5] != other.0[5] {
            return self.0[5].cmp(&other.0[5]);
        }
        if self.0[6] != other.0[6] {
            return self.0[6].cmp(&other.0[6]);
        }

        self.0[7].cmp(&other.0[7])
    }
}

impl core::cmp::PartialOrd for U512 {
    #[inline]
    fn ge(&self, other: &Self) -> bool {
        if self.0[0] != other.0[0] {
            return self.0[0].gt(&other.0[0]);
        }
        if self.0[1] != other.0[1] {
            return self.0[1].gt(&other.0[1]);
        }
        if self.0[2] != other.0[2] {
            return self.0[2].gt(&other.0[2]);
        }
        if self.0[3] != other.0[3] {
            return self.0[3].gt(&other.0[3]);
        }
        if self.0[4] != other.0[4] {
            return self.0[4].gt(&other.0[4]);
        }
        if self.0[5] != other.0[5] {
            return self.0[5].gt(&other.0[5]);
        }
        if self.0[6] != other.0[6] {
            return self.0[6].gt(&other.0[6]);
        }

        self.0[7].ge(&other.0[7])
    }

    #[inline]
    fn le(&self, other: &Self) -> bool {
        if self.0[0] != other.0[0] {
            return self.0[0].lt(&other.0[0]);
        }
        if self.0[1] != other.0[1] {
            return self.0[1].lt(&other.0[1]);
        }
        if self.0[2] != other.0[2] {
            return self.0[2].lt(&other.0[2]);
        }
        if self.0[3] != other.0[3] {
            return self.0[3].lt(&other.0[3]);
        }
        if self.0[4] != other.0[4] {
            return self.0[4].lt(&other.0[4]);
        }
        if self.0[5] != other.0[5] {
            return self.0[5].lt(&other.0[5]);
        }
        if self.0[6] != other.0[6] {
            return self.0[6].lt(&other.0[6]);
        }

        self.0[7].le(&other.0[7])
    }

    #[inline]
    fn gt(&self, other: &Self) -> bool {
        if self.0[0] != other.0[0] {
            return self.0[0].gt(&other.0[0]);
        }
        if self.0[1] != other.0[1] {
            return self.0[1].gt(&other.0[1]);
        }
        if self.0[2] != other.0[2] {
            return self.0[2].gt(&other.0[2]);
        }
        if self.0[3] != other.0[3] {
            return self.0[3].gt(&other.0[3]);
        }
        if self.0[4] != other.0[4] {
            return self.0[4].gt(&other.0[4]);
        }
        if self.0[5] != other.0[5] {
            return self.0[5].gt(&other.0[5]);
        }
        if self.0[6] != other.0[6] {
            return self.0[6].gt(&other.0[6]);
        }

        self.0[7].gt(&other.0[7])
    }

    #[inline]
    fn lt(&self, other: &Self) -> bool {
        if self.0[0] != other.0[0] {
            return self.0[0].lt(&other.0[0]);
        }
        if self.0[1] != other.0[1] {
            return self.0[1].lt(&other.0[1]);
        }
        if self.0[2] != other.0[2] {
            return self.0[2].lt(&other.0[2]);
        }
        if self.0[3] != other.0[3] {
            return self.0[3].lt(&other.0[3]);
        }
        if self.0[4] != other.0[4] {
            return self.0[4].lt(&other.0[4]);
        }
        if self.0[5] != other.0[5] {
            return self.0[5].lt(&other.0[5]);
        }
        if self.0[6] != other.0[6] {
            return self.0[6].lt(&other.0[6]);
        }

        self.0[7].lt(&other.0[7])
    }

    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl core::str::FromStr for U512 {
    type Err = ParseUintError;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.starts_with("0x") {
            Self::from_string_radix_pow_2(s, 16)
        } else if s.starts_with("0b") {
            Self::from_string_radix_pow_2(s, 2)
        } else if s.starts_with("0o") {
            Self::from_string_radix_pow_2(s, 8)
        } else {
            Self::from_string(s)
        }
    }
}

impl From<super::u256::U256> for U512 {
    #[inline]
    fn from(value: super::u256::U256) -> Self {
        let val = value.get_raw();
        Self([0, 0, 0, 0, val[0], val[1], val[2], val[3]])
    }
}

impl From<u128> for U512 {
    #[inline]
    fn from(value: u128) -> Self {
        Self([0, 0, 0, 0, 0, 0, (value >> 64) as u64, value as u64])
    }
}

impl From<u64> for U512 {
    #[inline]
    fn from(value: u64) -> Self {
        Self([0, 0, 0, 0, 0, 0, 0, value])
    }
}

impl From<u32> for U512 {
    #[inline]
    fn from(value: u32) -> Self {
        Self([0, 0, 0, 0, 0, 0, 0, value as u64])
    }
}

impl From<u16> for U512 {
    #[inline]
    fn from(value: u16) -> Self {
        Self([0, 0, 0, 0, 0, 0, 0, value as u64])
    }
}

impl From<u8> for U512 {
    #[inline]
    fn from(value: u8) -> Self {
        Self([0, 0, 0, 0, 0, 0, 0, value as u64])
    }
}

impl From<U512> for u128 {
    #[inline]
    fn from(value: U512) -> Self {
        ((value.0[6] as u128) << 64) | (value.0[7] as u128)
    }
}

impl From<U512> for super::u256::U256 {
    #[inline]
    fn from(value: U512) -> Self {
        Self::raw([value.0[4], value.0[5], value.0[6], value.0[7]])
    }
}

impl Into<u64> for U512 {
    #[inline]
    fn into(self) -> u64 {
        self.0[7]
    }
}

impl Into<u32> for U512 {
    #[inline]
    fn into(self) -> u32 {
        self.0[7] as u32
    }
}

impl Into<u16> for U512 {
    #[inline]
    fn into(self) -> u16 {
        self.0[7] as u16
    }
}

impl Into<u8> for U512 {
    #[inline]
    fn into(self) -> u8 {
        self.0[7] as u8
    }
}

impl core::ops::Add<U512> for U512 {
    type Output = U512;

    #[inline(always)]
    fn add(self, rhs: U512) -> Self::Output {
        self.add_internal(rhs)
    }
}

impl core::ops::AddAssign<U512> for U512 {
    #[inline(always)]
    fn add_assign(&mut self, rhs: U512) {
        *self = self.add_internal(rhs)
    }
}

impl core::ops::Sub<U512> for U512 {
    type Output = Self;

    #[inline(always)]
    fn sub(self, rhs: U512) -> Self::Output {
        self.sub_internal(rhs)
    }
}

impl core::ops::SubAssign<U512> for U512 {
    #[inline(always)]
    fn sub_assign(&mut self, rhs: U512) {
        *self = self.sub_internal(rhs)
    }
}

impl core::ops::Mul<U512> for U512 {
    type Output = U512;
    #[inline(always)]
    fn mul(self, other: U512) -> Self::Output {
        self.mul_internal(other)
    }
}

impl core::ops::MulAssign<U512> for U512 {
    #[inline(always)]
    fn mul_assign(&mut self, other: U512) {
        *self = self.mul_internal(other)
    }
}

impl core::ops::Mul<u64> for U512 {
    type Output = U512;
    #[inline(always)]
    fn mul(self, rhs: u64) -> Self::Output {
        self.mul_single_other(rhs)
    }
}

impl core::ops::MulAssign<u64> for U512 {
    #[inline(always)]
    fn mul_assign(&mut self, rhs: u64) {
        *self = self.mul_single_other(rhs)
    }
}

impl core::ops::Div<U512> for U512 {
    type Output = U512;
    #[inline(always)]
    fn div(self, other: U512) -> Self::Output {
        self.div_internal(other)
    }
}

impl core::ops::DivAssign<U512> for U512 {
    #[inline(always)]
    fn div_assign(&mut self, other: U512) {
        *self = self.div_internal(other)
    }
}

impl core::ops::Div<u64> for U512 {
    type Output = U512;
    #[inline(always)]
    fn div(self, rhs: u64) -> Self::Output {
        self.div_single(rhs)
    }
}

impl core::ops::DivAssign<u64> for U512 {
    #[inline(always)]
    fn div_assign(&mut self, rhs: u64) {
        *self = self.div_single(rhs)
    }
}

impl core::ops::Rem<U512> for U512 {
    type Output = U512;
    #[inline(always)]
    fn rem(self, other: U512) -> Self::Output {
        self.rem_internal(other)
    }
}

impl core::ops::RemAssign<U512> for U512 {
    #[inline(always)]
    fn rem_assign(&mut self, other: U512) {
        *self = self.rem_internal(other)
    }
}

impl core::ops::Rem<u64> for U512 {
    type Output = U512;
    #[inline(always)]
    fn rem(self, rhs: u64) -> Self::Output {
        self.rem_single(rhs)
    }
}

impl core::ops::RemAssign<u64> for U512 {
    #[inline(always)]
    fn rem_assign(&mut self, rhs: u64) {
        *self = self.rem_single(rhs)
    }
}

impl core::ops::Shl<u32> for U512 {
    type Output = Self;

    #[inline(always)]
    fn shl(self, rhs: u32) -> Self::Output {
        self.shift_left_internal(rhs)
    }
}

impl core::ops::ShlAssign<u32> for U512 {
    #[inline(always)]
    fn shl_assign(&mut self, rhs: u32) {
        *self = self.shift_left_internal(rhs)
    }
}

impl core::ops::Shr<u32> for U512 {
    type Output = Self;

    #[inline(always)]
    fn shr(self, rhs: u32) -> Self::Output {
        self.shift_right_internal(rhs)
    }
}

impl core::ops::ShrAssign<u32> for U512 {
    #[inline(always)]
    fn shr_assign(&mut self, rhs: u32) {
        *self = self.shift_right_internal(rhs)
    }
}

impl core::ops::BitAnd<U512> for U512 {
    type Output = Self;

    #[inline(always)]
    fn bitand(self, rhs: U512) -> Self::Output {
        Self([
            self.0[0] & rhs.0[0],
            self.0[1] & rhs.0[1],
            self.0[2] & rhs.0[2],
            self.0[3] & rhs.0[3],
            self.0[4] & rhs.0[4],
            self.0[5] & rhs.0[5],
            self.0[6] & rhs.0[6],
            self.0[7] & rhs.0[7],
        ])
    }
}

impl core::ops::BitAnd<u64> for U512 {
    type Output = Self;

    #[inline(always)]
    fn bitand(self, rhs: u64) -> Self::Output {
        Self([
            self.0[0],
            self.0[1],
            self.0[2],
            self.0[3],
            self.0[4],
            self.0[5],
            self.0[6],
            self.0[7] & rhs,
        ])
    }
}

impl core::ops::BitAndAssign<U512> for U512 {
    #[inline(always)]
    fn bitand_assign(&mut self, rhs: U512) {
        *self = Self([
            self.0[0] & rhs.0[0],
            self.0[1] & rhs.0[1],
            self.0[2] & rhs.0[2],
            self.0[3] & rhs.0[3],
            self.0[4] & rhs.0[4],
            self.0[5] & rhs.0[5],
            self.0[6] & rhs.0[6],
            self.0[7] & rhs.0[7],
        ])
    }
}

impl core::ops::BitAndAssign<u64> for U512 {
    #[inline(always)]
    fn bitand_assign(&mut self, rhs: u64) {
        *self = Self([
            self.0[0],
            self.0[1],
            self.0[2],
            self.0[3],
            self.0[4],
            self.0[5],
            self.0[6],
            self.0[7] & rhs,
        ])
    }
}

impl core::ops::BitOr<U512> for U512 {
    type Output = Self;

    #[inline(always)]
    fn bitor(self, rhs: U512) -> Self::Output {
        Self([
            self.0[0] | rhs.0[0],
            self.0[1] | rhs.0[1],
            self.0[2] | rhs.0[2],
            self.0[3] | rhs.0[3],
            self.0[4] | rhs.0[4],
            self.0[5] | rhs.0[5],
            self.0[6] | rhs.0[6],
            self.0[7] | rhs.0[7],
        ])
    }
}

impl core::ops::BitOr<u64> for U512 {
    type Output = Self;

    #[inline(always)]
    fn bitor(self, rhs: u64) -> Self::Output {
        Self([
            self.0[0],
            self.0[1],
            self.0[2],
            self.0[3],
            self.0[4],
            self.0[5],
            self.0[6],
            self.0[7] | rhs,
        ])
    }
}

impl core::ops::BitOrAssign<U512> for U512 {
    #[inline(always)]
    fn bitor_assign(&mut self, rhs: U512) {
        *self = Self([
            self.0[0] | rhs.0[0],
            self.0[1] | rhs.0[1],
            self.0[2] | rhs.0[2],
            self.0[3] | rhs.0[3],
            self.0[4] | rhs.0[4],
            self.0[5] | rhs.0[5],
            self.0[6] | rhs.0[6],
            self.0[7] | rhs.0[7],
        ])
    }
}

impl core::ops::BitOrAssign<u64> for U512 {
    #[inline(always)]
    fn bitor_assign(&mut self, rhs: u64) {
        *self = Self([
            self.0[0],
            self.0[1],
            self.0[2],
            self.0[3],
            self.0[4],
            self.0[5],
            self.0[6],
            self.0[7] | rhs,
        ])
    }
}

impl core::ops::BitXor<U512> for U512 {
    type Output = Self;

    #[inline(always)]
    fn bitxor(self, rhs: U512) -> Self::Output {
        Self([
            self.0[0] ^ rhs.0[0],
            self.0[1] ^ rhs.0[1],
            self.0[2] ^ rhs.0[2],
            self.0[3] ^ rhs.0[3],
            self.0[4] ^ rhs.0[4],
            self.0[5] ^ rhs.0[5],
            self.0[6] ^ rhs.0[6],
            self.0[7] ^ rhs.0[7],
        ])
    }
}

impl core::ops::BitXor<u64> for U512 {
    type Output = Self;

    #[inline(always)]
    fn bitxor(self, rhs: u64) -> Self::Output {
        Self([
            self.0[0],
            self.0[1],
            self.0[2],
            self.0[3],
            self.0[4],
            self.0[5],
            self.0[6],
            self.0[7] ^ rhs,
        ])
    }
}

impl core::ops::BitXorAssign<U512> for U512 {
    #[inline(always)]
    fn bitxor_assign(&mut self, rhs: U512) {
        *self = Self([
            self.0[0] ^ rhs.0[0],
            self.0[1] ^ rhs.0[1],
            self.0[2] ^ rhs.0[2],
            self.0[3] ^ rhs.0[3],
            self.0[4] ^ rhs.0[4],
            self.0[5] ^ rhs.0[5],
            self.0[6] ^ rhs.0[6],
            self.0[7] ^ rhs.0[7],
        ])
    }
}

impl core::ops::BitXorAssign<u64> for U512 {
    #[inline(always)]
    fn bitxor_assign(&mut self, rhs: u64) {
        *self = Self([
            self.0[0],
            self.0[1],
            self.0[2],
            self.0[3],
            self.0[4],
            self.0[5],
            self.0[6],
            self.0[7] ^ rhs,
        ])
    }
}

#[cfg(test)]
mod test {
    use super::{count_bits, ParseUintError, U512};

    #[test]
    fn gen_test() -> Result<(), ParseUintError> {
        let value = U512::from_string("12345678919")?;
        assert!(value.raw_eq([0, 0, 0, 0, 0, 0, 0, 12345678919]));

        // Equal to 1 << 64 = 18446744073709551616
        let value = U512::from_string("18446744073709551616")?;
        assert_eq!(value.0, ([0, 0, 0, 0, 0, 0, 1, 0]));

        // Equal to 1 << 128
        let value =
            U512::from_string("340282366920938463463374607431768211456")?;
        assert_eq!(value.0, ([0, 0, 0, 0, 0, 1, 0, 0]));

        // Equal to 115792089237316195423570985008687907852837564279074904382605163141518161494337
        let value = U512::from_string("115792089237316195423570985008687907852837564279074904382605163141518161494337")?;
        assert_eq!(
            value,
            U512([
                0,
                0,
                0,
                0,
                18446744073709551615,
                18446744073709551614,
                13451932020343611451,
                13822214165235122497
            ])
        );

        let value = U512::from_string("16983810465656793445178183341822322175883642221536626637512293983324")?;
        assert_eq!(
            value,
            U512([
                0,
                0,
                0,
                0,
                0xa1455b33,
                0x4df099df30fc28a1,
                0x69a467e9e47075a9,
                0x0f7e650eb6b7a45c
            ])
        );

        // Max value of 256-bit number
        let value = U512::from_string("115792089237316195423570985008687907853269984665640564039457584007913129639935")?;
        assert_eq!(
            value,
            U512([
                0,
                0,
                0,
                0,
                0xFFFF_FFFF_FFFF_FFFF,
                0xFFFF_FFFF_FFFF_FFFF,
                0xFFFF_FFFF_FFFF_FFFF,
                0xFFFF_FFFF_FFFF_FFFF,
            ])
        );

        // Max value of 512-bit number
        let value = "13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084095".parse::<U512>()?;
        assert_eq!(value, U512::MAX);

        Ok(())
    }

    #[test]
    fn test_bits() {
        assert_eq!(count_bits(0b01011100), 4);
        assert_eq!(count_bits(0b01_1100_1111_0011_1110_1001), 14);
    }

    #[test]
    fn test_add() -> Result<(), ParseUintError> {
        let a = U512::from_string("1245")?;
        let b = U512::from_string("4546477")?;
        let c = a + b;

        assert_eq!(c.0, U512::from_string("4547722")?.0);

        let a = U512::raw([
            0,
            0,
            0,
            0,
            0,
            0xFFFF_FFFF_FFFF_FFFF,
            0xFFFF_FFFF_FFFF_FFFF,
            0xFFFF_FFFF_FFFF_FFFF,
        ]);
        let b = U512::raw([
            0,
            0,
            0,
            0,
            0,
            0xFFFF_FFFF_FFFF_FFFF,
            0xFFFF_FFFF_FFFF_FFFF,
            0xFFFF_FFFF_FFFF_FFFF,
        ]);
        let c = a + b;
        assert_eq!(
            c,
            U512([
                0,
                0,
                0,
                0,
                0x1,
                0xFFFF_FFFF_FFFF_FFFF,
                0xFFFF_FFFF_FFFF_FFFF,
                0xFFFF_FFFF_FFFF_FFFE
            ])
        );

        Ok(())
    }

    #[test]
    fn test_sub() -> Result<(), ParseUintError> {
        let a = U512::from_string("12131414122")?;
        let b = U512::from_string("4546477")?;
        let c = a - b;

        assert_eq!(c, U512::from_string("12126867645")?);

        // Finite Field for secp256k1 (2^256 - 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1)
        // Source: https://en.bitcoin.it/wiki/Secp256k1
        let p = (U512::ONE << 256)
            - (U512::ONE << 32)
            - (U512::ONE << 9)
            - (U512::ONE << 8)
            - (U512::ONE << 7)
            - (U512::ONE << 6)
            - (U512::ONE << 4)
            - U512::ONE;

        assert_eq!(p, "0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFE_FFFF_FC2F".parse::<U512>()?);

        Ok(())
    }

    #[test]
    fn test_format() -> Result<(), ParseUintError> {
        let p = "231242904832985791475347973284762319417543905832485934759832598346782893471290".parse::<U512>()?;
        assert_eq!(
            format!("{}", p),
            "231242904832985791475347973284762319417543905832485934759832598346782893471290"
        );
        assert_eq!(
            format!("{:x}", p),
            "0x1ff3ed89117e70e5eebcefe04bc75a8fa9ca86dbaa1dd29d762541238963cf63a"
        );
        Ok(())
    }

    #[test]
    fn test_mul_single() -> Result<(), ParseUintError> {
        let a = U512::from_string("124312312142135")?;
        let b = 4546477;
        let c = a * b;

        assert_eq!(c.0, U512::from_string("565183067971037508395")?.0);

        let a = U512::from_string("29408993404948928992877151431649155974")?;
        let b = 2132132112312312321;
        let c = a * b;

        assert_eq!(
            c.0,
            U512::from_string(
                "62703859229472622214294486738735594201348857847930955654"
            )?
            .0
        );

        Ok(())
    }

    #[test]
    fn test_mul() -> Result<(), ParseUintError> {
        let a = U512::from_string("1231242")?;
        let b = U512::from_string("42145124")?;
        let c = a * b;
        assert_eq!(c, U512::from_string("51890846764008")?);

        // Multiply 1 << 64 with 1 << 64
        let a = U512::ONE << 64;
        let b = U512::ONE << 64;
        let c = a * b;
        assert_eq!(c, U512::ONE << 128);

        let a = U512::from_string("29408993404948928992877151431649155974")?;
        let b = U512::from_string("213213211231231232131232142142421312")?;
        let c = a * b;

        assert_eq!(
            c,
            "6270385922947262222347954536162455298520515727022267860678267425509717888".parse::<U512>()?
        );

        Ok(())
    }

    #[test]
    fn test_shift_bits() -> Result<(), ParseUintError> {
        let mut a = U512::from_string("940899340494892899287232132141")?;
        a <<= 98;

        assert_eq!(
            a,
            U512::from_string(
                "298182903433174043516747888242818498075070855821604373397504"
            )?
        );

        assert_eq!(
            a >> 1,
            "149091451716587021758373944121409249037535427910802186698752"
                .parse::<U512>()?
        );

        assert_eq!(a >> 178, U512::from_string("778293")?);
        assert_eq!(a << 22, U512::from_string("1250669744601375623418469734648406597750261990855978509758644617216")?);
        assert_eq!(a << 25, U512::from_string("10005357956811004987347757877187252782002095926847828078069156937728")?);

        Ok(())
    }

    #[test]
    fn test_div() -> Result<(), ParseUintError> {
        let a = U512::from_string("29408993404948928992877151431649155974")?;
        let b = 123456566;
        let c = a / b;

        assert_eq!(c, U512::from_string("238213279032473080393935073746")?);

        let a = U512::from_string(
            "294089934049489289928723213214128471823791287151431649155974",
        )?;
        let b = U512::from_string("940899340494892899287232132141")?;
        let c = a / b;

        assert_eq!(c, U512::from_string("312562589208325179552885042139")?);

        let a = U512::from_string("3912093812908391208428194902184908123982189742178629873982173391238912")?;
        let b = U512::from_string(
            "940899340494892899287232134329048329473287439824732982141",
        )?;
        let c = a / b;

        assert_eq!(c, U512::from_string("4157823950488")?);

        let a = U512::from_string("1032105389620138683259824866402890871739720549422559896654845224087")?;
        let b = U512::from_string("51248759832749832749873129879328147")?;
        let c = a / b;

        assert_eq!(c, U512::from_string("20139129083092183902183912839021")?);

        Ok(())
    }

    #[test]
    fn test_rem() -> Result<(), ParseUintError> {
        let a = U512::from_string("29408993404948928992877151431649155974")?;
        let b = 123456566;
        let c = a % b;

        assert_eq!(c, U512::from_string("11239738")?);

        let a = U512::from_string(
            "294089934049489289928723213214128471823791287151431649155974",
        )?;
        let b = "940899340494892899287232132141".parse::<U512>()?;

        assert_eq!(a % b, "229622695252588468980047866375".parse::<U512>()?);

        let a = "3912093812908391208428194902184908123982189742178629873982173391238912".parse::<U512>()?;
        let b = "940899340494892899287232134329048329473287439824732982141"
            .parse::<U512>()?;
        let c = a % b;

        assert_eq!(
            c,
            "361780925295470009804517438088754858207007846931619004104"
                .parse::<U512>()?
        );

        let a = "1032105389620138683259824866402890871739720549422559896654845224087".parse::<U512>()?;
        let b = "51248759832749832749873129879328147".parse::<U512>()?;
        let c = a % b;

        assert_eq!(c.is_zero(), true);

        Ok(())
    }
}

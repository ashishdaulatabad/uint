#![feature(error_in_core)]
#![no_std]

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

pub mod u256;

#![feature(test)]

extern crate test;

use big_num_math::{pg, PrimeGenErr, PrimeGenRes, PrimeGenStrain};
use std::time::{Duration, Instant};
use test::Bencher;

#[bench]
fn u64(b: &mut Bencher) {
    b.iter(|| {
        let num = || pg!(20_000, PrimeGenStrain::Nth, false, u64, None);
        assert_eq!(Ok(PrimeGenRes::Max(224_737)), num());
    });
}

#[bench]
fn u32(b: &mut Bencher) {
    b.iter(|| {
        let num = || pg!(20_000, PrimeGenStrain::Nth, false, u32, None);
        assert_eq!(Ok(PrimeGenRes::Max(224_737)), num());
    });
}

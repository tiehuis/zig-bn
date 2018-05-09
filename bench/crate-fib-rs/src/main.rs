extern crate num_bigint;
extern crate num_traits;

use num_bigint::BigInt;
use num_traits::One;

const TARGET: u32 = 200000;

fn main() {
    let mut f0: BigInt = One::one();
    let mut f1: BigInt = One::one();

    for _ in 0..TARGET {
        f1 = &f1 + &f0;
        f0 = &f1 - &f0;
    }

    // print!("{}", f1);
}

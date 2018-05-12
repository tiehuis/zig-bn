extern crate num_bigint;
extern crate num_traits;

use num_bigint::BigInt;
use num_traits::One;

const TARGET: u32 = 20000;

fn main() {
    let mut f: BigInt = One::one();
    let mut c: BigInt = One::one();
    let one: BigInt = One::one();

    for _ in 0..TARGET {
        f = &f * &c;
        c = &c + &one;
    }

    let mut i = TARGET - 1;
    while i != 0 {
        f = &f / &c;
        c = &c - &one;
        i -= 1;
    }

    print!("{:x}", f);
}

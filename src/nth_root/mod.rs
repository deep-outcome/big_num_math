// Let α be the next n digits of the radicand.
pub struct AlphaGenerator<'a> {
    // operative number
    num: &'a [u8],
    // slice index
    ix: usize,
    // radix size
    ras: usize,
    // zero
    zer: [u8; 1],
}

impl<'a> AlphaGenerator<'a> {
    pub fn new(num: &'a [u8], ras: usize) -> Self {
        if ras == 0 {
            panic!("0ᵗʰ root is strictly unsupported computation.");
            // that would mean seeking such root that is result of zero-time
            // applied division, that means root is argument but this would
            // be possible only for 0 and 1
        }

        let places = num.len();

        let full_blocks = places / ras;
        let fbs_size = full_blocks * ras;
        let divisible = fbs_size == places;

        let ix = match divisible {
            true => places - ras,
            false => fbs_size,
        };

        Self {
            num,
            ras,
            ix,
            zer: [0],
        }
    }

    pub fn next(&mut self) -> &[u8] {
        let num = self.num;

        if num.len() == 0 {
            return &self.zer;
        }

        let ix = self.ix;
        let alpha = &num[ix..];
        self.num = &num[..ix];

        if ix > 0 {
            self.ix = ix - self.ras;
        }

        alpha
    }
}

#[cfg(test)]
mod tests_of_units {

    mod alpha_generator {
        use super::super::AlphaGenerator;

        use crate::new_from_num;

        use crate::{nought_raw, Row};
        use std::ops::Deref;

        #[test]
        fn lesser_root_test() {
            let vals = [
                (1_234_567, 3, [1, 234, 567, 0, 0]),
                (11_2222_3333, 4, [11, 2222, 3333, 0, 0]),
            ];

            for v in vals {
                let num = new_from_num!(v.0);
                let mut generator = AlphaGenerator::new(num.deref(), v.1);

                for p in v.2 {
                    let proof = new_from_num!(p).row;

                    let next = generator.next();
                    assert_eq!(proof, next);
                }
            }
        }

        #[test]
        fn greater_root_test() {
            let vals = [
                (123, 4, [123, 0, 0]),
                (123, 11, [123, 0, 0]),
                (12345_67890, 11, [12345_67890, 0, 0]),
            ];

            for v in vals {
                let num = new_from_num!(v.0);
                let mut generator = AlphaGenerator::new(num.deref(), v.1);

                for p in v.2 {
                    let proof = new_from_num!(p).row;

                    let next = generator.next();
                    assert_eq!(proof, next);
                }
            }
        }

        #[test]
        fn divisible_by_root_test() {
            let vals = [
                (1_234_567, 7, [1_234_567, 0, 0, 0, 0, 0]),
                (11_2222_3333, 2, [11, 22, 22, 33, 33, 0]),
                (333_444_555, 3, [333, 444, 555, 0, 0, 0]),
            ];

            for v in vals {
                let num = new_from_num!(v.0);
                let mut generator = AlphaGenerator::new(num.deref(), v.1);

                for p in v.2 {
                    let proof = new_from_num!(p).row;

                    let next = generator.next();
                    assert_eq!(proof, next);
                }
            }
        }

        #[test]
        fn zero_num_test() {
            let number = [0];
            let root = 1;

            let mut generator = AlphaGenerator::new(number.as_slice(), root);

            let proof = nought_raw();
            for _ in 0..3 {
                let next = generator.next();
                assert_eq!(proof, next);
            }
        }

        #[test]
        #[should_panic(expected = "0ᵗʰ root is strictly unsupported computation.")]
        fn zero_root_test() {
            let number = new_from_num!(u32::MAX);
            let root = 0;

            _ = AlphaGenerator::new(number.deref(), root);
        }
    }
}

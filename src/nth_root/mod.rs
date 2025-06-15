use super::{mul, pow};
use crate::PlacesRow;

fn base() -> PlacesRow {
    PlacesRow { row: vec![0, 1] }
}

// think of shortcuts
// any root of 0 = 0
// any root of 1 = 1

// pub const fn nth_root(nth: u16, rad: &PlacesRow) -> Option<PlacesRow> {
//     if nth == 0 {
//         return None;
//     }
//
//     // root/radix
//     // y
//     let mut rax = 0;
//     // remainder
//     // r
//     let mut rem = 0;
//
//     let base = base();
//
//     // decadic base powered by degree
//     // base degree power
//     // Bⁿ
//     let bdp = pow(&base, nth);
//
//     // n -1
//     let nth_less = nth - 1;
//
//     // degree base degree less power
//     // nBⁿ⁻¹
//     let nth_pr = PlacesRow::new_from_u16(nth);
//     let dbdlp = mul(&nth_pr, &pow(&base, nth));
//
//     let mut agen = AlphaGenerator::new(rad, nth);
//
//     // integer root, otherwise some kind (degree) of precision must be used
//     loop {
//         // α
//         let alpha = agen.next();
//         // operatives
//         // y', r'
//         let (orax, orem) = super::step::next(rax, rem, bdp, alpha, nth, nth_less, dbdlp);
//
//         let orax_pow = orax.pow(nth);
//
//         if orax_pow > rad {
//             break;
//         }
//
//         rax = orax;
//
//         if orax_pow == rad {
//             break;
//         }
//
//         rem = orem;
//     }
//
//     Some(rax)
// }

// mod step {
//     const fn next_actual(
//         mut rax: u32,     // y
//         rem: u32,         // r
//         bdp: u32,         // Bⁿ
//         alpha: u32,       // α
//         degree: u32,      // n
//         degree_less: u32, // n -1
//         dbdlp: u32,       // nBⁿ⁻¹
//     ) -> (u32, u32) {
//         // By, widen rax
//         let wrax = rax * super::BASE;
//
//         // yⁿ⁻¹
//         let rax_pow_less = rax.pow(degree_less);
//
//         // Bⁿyⁿ, subtrahend
//         let sub = bdp * (rax_pow_less * rax);
//         // Bⁿr +α, limit
//         let lim = bdp * rem + alpha;
//
//         // y' =By +β, β =0
//         rax = wrax;
//
//         // (By +β)ⁿ -Bⁿyⁿ
//         // β =0 =>(By)ⁿ -Bⁿyⁿ =0
//         let mut max = 0;
//
//         // let make initial guess, if possible
//         let (guess, beta) = {
//             let mut g = 0;
//
//             if rax_pow_less > 0 {
//                 // nBⁿ⁻¹ ·yⁿ⁻¹
//                 let div = dbdlp * rax_pow_less;
//
//                 // Bⁿr +α ÷(nBⁿ⁻¹ ·yⁿ⁻¹)
//                 g = lim / div;
//             }
//
//             if g > 1 {
//                 (Some(g), g)
//             } else {
//                 (None, 1)
//             }
//         };
//
//         let incr_res = incr(wrax, beta, degree, sub, lim, guess, rax, max);
//
//         if let Some((orax, omax)) = incr_res {
//
//             (rax, max) = (orax, omax);
//         } else {
//
//             (rax, max) = decr(wrax, beta, degree, sub, lim);
//         }
//
//         // r' =Bⁿr +α -((By +β)ⁿ -Bⁿyⁿ)
//         (rax, lim - max)
//     }
//
//     const fn incr(
//         wrax: u32,
//         mut beta: u32,
//         degree: u32,
//         sub: u32,
//         lim: u32,
//         guess: Option<u32>,
//         mut rax: u32,
//         mut max: u32,
//     ) -> Option<(u32, u32)> {
//         // seeking largest beta that
//         // (By +β)ⁿ -Bⁿyⁿ ≤ Bⁿr +α
//         loop {
//             // o stands for operative
//
//             // y' =By +β
//             let orax = wrax + beta;
//             // (By +β)ⁿ
//             let orax_deg_pow = orax.pow(degree);
//             // (By +β)ⁿ -Bⁿyⁿ
//             let omax = orax_deg_pow - sub;
//
//             // (By +β)ⁿ -Bⁿyⁿ ≤ Bⁿr +α
//             if omax > lim {
//                 if let Some(g) = guess {
//                     if g == beta {
//                         return None;
//                     }
//                 }
//
//                 return Some((rax, max));
//             }
//
//             rax = orax;
//             max = omax;
//
//             // (By +β)ⁿ -Bⁿyⁿ ≤ Bⁿr +α
//             if omax == lim {
//                 return Some((rax, max));
//             }
//
//             beta += 1;
//         }
//     }
//
//     const fn decr(wrax: u32, mut beta: u32, degree: u32, sub: u32, lim: u32) -> (u32, u32) {
//         // seeking largest beta that
//         // (By +β)ⁿ -Bⁿyⁿ ≤ Bⁿr +α
//         beta -= 1;
//         loop {
//             // o stands for operative
//
//             // y' =By +β
//             let orax = wrax + beta;
//             // (By +β)ⁿ
//             let orax_deg_pow = orax.pow(degree);
//             // (By +β)ⁿ -Bⁿyⁿ
//             let omax = orax_deg_pow - sub;
//
//             // (By +β)ⁿ -Bⁿyⁿ ≤ Bⁿr +α
//             if omax <= lim {
//                 return (orax, omax);
//             }
//
//             beta -= 1;
//         }
//     }
// }

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

    //
    //         mod root {
    //
    //             use super::super::root;
    //
    //             #[test]
    //             fn basic_test() {
    //                 assert_eq!(Some(2), root(3, 8));
    //             }
    //
    //             #[test]
    //             fn zero_root_test() {
    //                 assert_eq!(None, root(0, u32::MAX));
    //             }
    //
    //             #[test]
    //             fn first_root_test() {
    //                 let vals = [0, 1, 2, 3, 10, 100, 999, 1_000_000, 9_999_999];
    //
    //                 for &v in vals.iter() {
    //                     assert_eq!(Some(v), root(1, v), "val: {v}");
    //                 }
    //             }
    //
    //             #[test]
    //             fn sqrt_basic_test() {
    //                 #[rustfmt::skip]
    //                             let vals = [
    //                                 (0, [0].as_slice()),
    //                                 (1, [1,3].as_slice()),
    //                                 (2, [4,8].as_slice()),
    //                                 (3, [9,15].as_slice()),
    //                                 (4, [16,24].as_slice()),
    //                                 (5, [25,35].as_slice())];
    //
    //                 for v in vals.iter() {
    //                     for &n in v.1 {
    //                         assert_eq!(Some(v.0), root(2, n), "exp: {}, inp: {}", v.0, n);
    //                     }
    //                 }
    //             }
    //
    //             #[test]
    //             fn cbrt_basic_test() {
    //                 #[rustfmt::skip]
    //                             let vals = [
    //                                 (0,[0].as_slice()),
    //                                 (1,[1,7].as_slice()),
    //                                 (2,[8,26].as_slice()),
    //                                 (3,[27,63].as_slice()),
    //                                 (4,[64,124].as_slice()),
    //                                 (5,[125,215].as_slice())];
    //
    //                 for v in vals.iter() {
    //                     for &n in v.1 {
    //                         assert_eq!(Some(v.0), root(3, n), "exp: {}, inp: {}", v.0, n);
    //                     }
    //                 }
    //             }
    //
    //             #[test]
    //             fn integer_root_test() {
    //                 #[rustfmt::skip]
    //                             let vals = [
    //                                 (4, 4, 256),
    //                                 (7, 5, 16_807),
    //                                 (100, 4, 1_00_00_00_00),
    //                                 (217, 3, 10_218_313),
    //                                 (5560, 2, 30_913_600),
    //                                 (1222, 3, 1_824_793_048),
    //                                 (177, 4, 981_506_241),
    //                                 (793, 3, 498_677_257),
    //                                 (313, 3, 30_664_297),
    //                                 // works only in release
    //                                 (4, 14, 268_435_456),
    //                                 (2, 30, 1_073_741_824),
    //                                 // ill-fated overflows
    //                                 // (2, 31, 2147483648),
    //                                 // (4, 15, 1073741824),
    //                             ];
    //                 for v in vals {
    //                     assert_eq!(
    //                         Some(v.0),
    //                         root(v.1, v.2),
    //                         "exp: {}, deg: {}, inp: {}",
    //                         v.0,
    //                         v.1,
    //                         v.2
    //                     );
    //                 }
    //             }
    //
    //             #[test]
    //             fn rounded_root_test() {
    //                 #[rustfmt::skip]
    //                             let vals = [
    //                                 (17, 2, 312),               // ≈ 17.7
    //                                 (9, 4, 9999),               // ≈ 9.9998
    //                                 (9, 3, 999),                // ≈ 9.997
    //                                 (9, 2, 99),                 // ≈ 9.95
    //                                 (99, 2, 9999),              // ≈ 99.995
    //                                 (21, 3, 9999),              // ≈ 21.5
    //                                 (20, 4, 173_479),           // ≈ 20.41
    //
    //                                 // works only in release
    //                                 // does not work with guess
    //                                 // (2, 17, 16_777_215),        // ≈ 2.661
    //                                 (3, 13, 33_554_431),        // ≈ 3.79
    //                                 (31629, 2, 1_000_400_400),  // ≈ 31629.11
    //                                 (45, 5, 200_300_010),       // ≈ 45.7
    //
    //                                 // ill-fated overflows
    //                                 // (5, 12, 900_900_009),    // ≈ 5.575
    //                                 // (2, 26, 90_900_009),     // ≈ 2.02
    //                             ];
    //                 for v in vals {
    //                     assert_eq!(
    //                         Some(v.0),
    //                         root(v.1, v.2),
    //                         "exp: {}, deg: {}, inp: {}",
    //                         v.0,
    //                         v.1,
    //                         v.2
    //                     );
    //                 }
    //             }
    //
    //             #[test]
    //             fn readme_test() {
    //                 assert_eq!(Some(3), root(13, 33_554_431));
    //                 assert_eq!(Some(5560), root(2, 30_913_600));
    //             }
    //         }
    //
    //         mod root_actual {
    //             use super::super::root_actual;
    //
    //             #[test]
    //             fn expected_escape_test() {
    //                 let mut bcode = 0;
    //
    //                 _ = root_actual(4, 256, &mut bcode, &mut 0, &mut 0, &mut 0);
    //                 assert_eq!(2, bcode);
    //
    //                 _ = root_actual(4, 257, &mut bcode, &mut 0, &mut 0, &mut 0);
    //                 assert_eq!(1, bcode);
    //             }
    //
    //             #[test]
    //             fn degree_one_test() {
    //                 let mut bdp_out = u32::MAX;
    //                 let mut nth_less_out = u32::MAX;
    //                 let mut dbdlp_out = u32::MAX;
    //
    //                 _ = root_actual(
    //                     1,
    //                     0,
    //                     &mut 0,
    //                     &mut bdp_out,
    //                     &mut nth_less_out,
    //                     &mut dbdlp_out,
    //                 );
    //
    //                 assert_eq!(10, bdp_out);
    //                 assert_eq!(0, nth_less_out);
    //                 assert_eq!(1, dbdlp_out);
    //             }
    //
    //             #[test]
    //             fn computational_test() {
    //                 let mut bdp_out = u32::MAX;
    //                 let mut nth_less_out = u32::MAX;
    //                 let mut dbdlp_out = u32::MAX;
    //
    //                 _ = root_actual(
    //                     9,
    //                     0,
    //                     &mut 0,
    //                     &mut bdp_out,
    //                     &mut nth_less_out,
    //                     &mut dbdlp_out,
    //                 );
    //
    //                 assert_eq!(1_000_000_000, bdp_out);
    //                 assert_eq!(8, nth_less_out);
    //                 assert_eq!(900_000_000, dbdlp_out);
    //             }
    //         }
}

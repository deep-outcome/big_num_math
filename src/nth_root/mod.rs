const fn next_actual(
    mut rax: u32,     // y
    rem: u32,         // r
    bdp: u32,         // Bⁿ
    alpha: u32,       // α
    degree: u32,      // n
    degree_less: u32, // n -1
    dbdlp: u32,       // nBⁿ⁻¹
    #[cfg(test)] wrax_out: &mut u32,
    #[cfg(test)] rax_pow_less_out: &mut u32,
    #[cfg(test)] sub_out: &mut u32,
    #[cfg(test)] lim_out: &mut u32,
    #[cfg(test)] div_out: &mut u32,
    #[cfg(test)] beta_out: &mut u32,
    #[cfg(test)] guess_out: &mut Option<u32>,
    #[cfg(test)] incr_out: &mut bool,
    #[cfg(test)] decr_out: &mut bool,
) -> (u32, u32) {
    // By, widen rax
    let wrax = rax * super::BASE;
    
    // yⁿ⁻¹
    let rax_pow_less = rax.pow(degree_less);
    
    // Bⁿyⁿ, subtrahend
    let sub = bdp * (rax_pow_less * rax);
    // Bⁿr +α, limit
    let lim = bdp * rem + alpha;
    
    // y' =By +β, β =0
    rax = wrax;
    
    // (By +β)ⁿ -Bⁿyⁿ
    // β =0 =>(By)ⁿ -Bⁿyⁿ =0
    let mut max = 0;
    
    // let make initial guess, if possible
    let (guess, beta) = {
        let mut g = 0;
        
        if rax_pow_less > 0 {
            // nBⁿ⁻¹ ·yⁿ⁻¹
            let div = dbdlp * rax_pow_less;
            
            #[cfg(test)]
            {
                *div_out = div;
            }
            
            // Bⁿr +α ÷(nBⁿ⁻¹ ·yⁿ⁻¹)
            g = lim / div;
        }
        
        if g > 1 {
            (Some(g), g)
        } else {
            (None, 1)
        }
    };
    
    #[cfg(test)]
    {
        *wrax_out = wrax;
        *rax_pow_less_out = rax_pow_less;
        *sub_out = sub;
        *lim_out = lim;
        *beta_out = beta;
        *guess_out = guess;
    }
    
    let res = incr(wrax, beta, degree, sub, lim, guess, rax, max);
    
    if let Some((orax, omax)) = res {
        #[cfg(test)]
        {
            *incr_out = true;
        }
        
        (rax, max) = (orax, omax);
    } else {
        #[cfg(test)]
        {
            *decr_out = true;
        }
        
        (rax, max) = decr(wrax, beta, degree, sub, lim);
    }
    
    // r' =Bⁿr +α -((By +β)ⁿ -Bⁿyⁿ)
    (rax, lim - max)
}

const fn incr(
    wrax: u32,
    mut beta: u32,
    degree: u32,
    sub: u32,
    lim: u32,
    guess: Option<u32>,
    mut rax: u32,
    mut max: u32,
) -> Option<(u32, u32)> {
    // seeking largest beta that
    // (By +β)ⁿ -Bⁿyⁿ ≤ Bⁿr +α
    loop {
        // o stands for operative
        
        // y' =By +β
        let orax = wrax + beta;
        // (By +β)ⁿ
        let orax_deg_pow = orax.pow(degree);
        // (By +β)ⁿ -Bⁿyⁿ
        let omax = orax_deg_pow - sub;
        
        // (By +β)ⁿ -Bⁿyⁿ ≤ Bⁿr +α
        if omax > lim {
            if let Some(g) = guess {
                if g == beta {
                    return None;
                }
            }
            
            return Some((rax, max));
        }
        
        rax = orax;
        max = omax;
        
        // (By +β)ⁿ -Bⁿyⁿ ≤ Bⁿr +α
        if omax == lim {
            return Some((rax, max));
        }
        
        beta += 1;
    }
}

const fn decr(wrax: u32, beta: u32, degree: u32, sub: u32, lim: u32) -> (u32, u32) {
    // o stands for operative
    // y' =By +β
    let mut orax = wrax + beta;
    
    // seeking largest beta that
    // (By +β)ⁿ -Bⁿyⁿ ≤ Bⁿr +α
    loop {
        orax = orax - 1;
        
        // (By +β)ⁿ
        let orax_deg_pow = orax.pow(degree);
        // (By +β)ⁿ -Bⁿyⁿ
        let omax = orax_deg_pow - sub;
        
        // (By +β)ⁿ -Bⁿyⁿ ≤ Bⁿr +α
        if omax <= lim {
            return (orax, omax);
        }
    }
}


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
    
    mod next_actual {
        use crate::step::next_actual;
        
        #[test]
        fn basic_test() {
            let rax = 3;
            let rem = 15;
            let bdp = 1000;
            let alpha = 133;
            let degree = 3;
            let degree_less = 2;
            let dbdlp = 300;
            
            let mut wrax_out = u32::MAX;
            let mut rax_pow_less_out = u32::MAX;
            let mut sub_out = u32::MAX;
            let mut lim_out = u32::MAX;
            let mut div_out = u32::MAX;
            let mut beta_out = u32::MAX;
            let mut guess_out = Some(u32::MAX);
            
            let res = next_actual(
                rax, rem, bdp, alpha, degree, degree_less, dbdlp, &mut wrax_out,
                &mut rax_pow_less_out, &mut sub_out, &mut lim_out, &mut div_out, &mut beta_out,
                &mut guess_out, &mut false, &mut false,
            );
            
            let sub = 27_000;
            let lim = 15_133;
            let div = 2700;
            
            assert_eq!(30, wrax_out);
            assert_eq!(9, rax_pow_less_out);
            assert_eq!(sub, sub_out);
            assert_eq!(lim, lim_out);
            assert_eq!(div, div_out);
            
            let beta = lim / div;
            assert_eq!(beta, beta_out);
            assert_eq!(Some(beta), guess_out);
            
            let rem = lim - (34u32.pow(degree) - sub);
            assert_eq!((34, rem), res)
        }
        
        #[test]
        fn rax_zero_test() {
            let rax = 0;
            let rem = 0;
            let bdp = 1000;
            let alpha = 133;
            let degree = 3;
            let degree_less = 2;
            let dbdlp = 300;
            
            let mut wrax_out = u32::MAX;
            let mut rax_pow_less_out = u32::MAX;
            let mut sub_out = u32::MAX;
            let mut lim_out = u32::MAX;
            let mut div_out = u32::MAX;
            let mut beta_out = u32::MAX;
            let mut guess_out = Some(u32::MAX);
            
            _ = next_actual(
                rax, rem, bdp, alpha, degree, degree_less, dbdlp, &mut wrax_out,
                &mut rax_pow_less_out, &mut sub_out, &mut lim_out, &mut div_out, &mut beta_out,
                &mut guess_out, &mut false, &mut false,
            );
            
            assert_eq!(0, wrax_out);
            assert_eq!(0, rax_pow_less_out);
            assert_eq!(0, sub_out);
            assert_eq!(133, lim_out);
            assert_eq!(u32::MAX, div_out);
            assert_eq!(1, beta_out);
            assert_eq!(None, guess_out);
        }
        
        #[test]
        fn degree_one_test() {
            let rax = 2;
            let rem = 3;
            let bdp = 10;
            let alpha = 222;
            let degree = 1;
            let degree_less = 0;
            let dbdlp = 1;
            
            let mut wrax_out = u32::MAX;
            let mut rax_pow_less_out = u32::MAX;
            let mut sub_out = u32::MAX;
            let mut lim_out = u32::MAX;
            let mut div_out = u32::MAX;
            let mut beta_out = u32::MAX;
            let mut guess_out = Some(u32::MAX);
            
            _ = next_actual(
                rax, rem, bdp, alpha, degree, degree_less, dbdlp, &mut wrax_out,
                &mut rax_pow_less_out, &mut sub_out, &mut lim_out, &mut div_out, &mut beta_out,
                &mut guess_out, &mut false, &mut false,
            );
            
            assert_eq!(20, wrax_out);
            assert_eq!(1, rax_pow_less_out);
            assert_eq!(20, sub_out);
            assert_eq!(252, lim_out);
            assert_eq!(1, div_out);
            assert_eq!(252, beta_out);
            assert_eq!(Some(252), guess_out);
        }
        
        #[test]
        fn g_zero_test() {
            let rax = 2;
            let rem = 1;
            let bdp = 1000;
            let alpha = 199;
            let degree = 3;
            let degree_less = 2;
            let dbdlp = 300;
            
            let mut wrax_out = u32::MAX;
            let mut rax_pow_less_out = u32::MAX;
            let mut sub_out = u32::MAX;
            let mut lim_out = u32::MAX;
            let mut div_out = u32::MAX;
            let mut beta_out = u32::MAX;
            let mut guess_out = Some(u32::MAX);
            
            _ = next_actual(
                rax, rem, bdp, alpha, degree, degree_less, dbdlp, &mut wrax_out,
                &mut rax_pow_less_out, &mut sub_out, &mut lim_out, &mut div_out, &mut beta_out,
                &mut guess_out, &mut false, &mut false,
            );
            
            assert_eq!(20, wrax_out);
            assert_eq!(4, rax_pow_less_out);
            assert_eq!(8000, sub_out);
            assert_eq!(1199, lim_out);
            assert_eq!(1200, div_out);
            assert_eq!(1, beta_out);
            assert_eq!(None, guess_out);
        }
        
        #[test]
        fn g_one_test() {
            let rax = 2;
            let rem = 2;
            let bdp = 1000;
            let alpha = 399;
            let degree = 3;
            let degree_less = 2;
            let dbdlp = 300;
            
            let mut wrax_out = u32::MAX;
            let mut rax_pow_less_out = u32::MAX;
            let mut sub_out = u32::MAX;
            let mut lim_out = u32::MAX;
            let mut div_out = u32::MAX;
            let mut beta_out = u32::MAX;
            let mut guess_out = Some(u32::MAX);
            
            _ = next_actual(
                rax, rem, bdp, alpha, degree, degree_less, dbdlp, &mut wrax_out,
                &mut rax_pow_less_out, &mut sub_out, &mut lim_out, &mut div_out, &mut beta_out,
                &mut guess_out, &mut false, &mut false,
            );
            
            assert_eq!(20, wrax_out);
            assert_eq!(4, rax_pow_less_out);
            assert_eq!(8000, sub_out);
            assert_eq!(2_399, lim_out);
            assert_eq!(1200, div_out);
            assert_eq!(1, beta_out);
            assert_eq!(None, guess_out);
        }
        
        #[test]
        fn g_two_test() {
            let rax = 2;
            let rem = 2;
            let bdp = 1000;
            let alpha = 400;
            let degree = 3;
            let degree_less = 2;
            let dbdlp = 300;
            
            let mut wrax_out = u32::MAX;
            let mut rax_pow_less_out = u32::MAX;
            let mut sub_out = u32::MAX;
            let mut lim_out = u32::MAX;
            let mut div_out = u32::MAX;
            let mut beta_out = u32::MAX;
            let mut guess_out = Some(u32::MAX);
            
            _ = next_actual(
                rax, rem, bdp, alpha, degree, degree_less, dbdlp, &mut wrax_out,
                &mut rax_pow_less_out, &mut sub_out, &mut lim_out, &mut div_out, &mut beta_out,
                &mut guess_out, &mut false, &mut false,
            );
            
            assert_eq!(20, wrax_out);
            assert_eq!(4, rax_pow_less_out);
            assert_eq!(8000, sub_out);
            assert_eq!(2_400, lim_out);
            assert_eq!(1200, div_out);
            assert_eq!(2, beta_out);
            assert_eq!(Some(2), guess_out);
        }
        
        #[test]
        fn incr_test() {
            let rax = 3;
            let rem = 4;
            let bdp = 1000;
            let alpha = 133;
            let degree = 3;
            let degree_less = 2;
            let dbdlp = 300;
            
            let mut incr_out = false;
            let mut decr_out = false;
            
            _ = next_actual(
                rax, rem, bdp, alpha, degree, degree_less, dbdlp, &mut 0, &mut 0, &mut 0,
                &mut 0, &mut 0, &mut 0, &mut None, &mut incr_out, &mut decr_out,
            );
            
            assert_eq!(true, incr_out);
            assert_eq!(false, decr_out);
        }
        
        #[test]
        fn decr_test() {
            let rax = 3;
            let rem = 15;
            let bdp = 1000;
            let alpha = 133;
            let degree = 3;
            let degree_less = 2;
            let dbdlp = 300;
            
            let mut incr_out = false;
            let mut decr_out = false;
            
            _ = next_actual(
                rax, rem, bdp, alpha, degree, degree_less, dbdlp, &mut 0, &mut 0, &mut 0,
                &mut 0, &mut 0, &mut 0, &mut None, &mut incr_out, &mut decr_out,
            );
            
            assert_eq!(false, incr_out);
            assert_eq!(true, decr_out);
        }
    }
    
    mod incr {
        use super::super::incr;
        
        #[test]
        fn guess_too_much_test() {
            let wrax = 20;
            let beta = 3;
            let degree = 3;
            let sub = 66;
            let lim = 12100;
            let guess = Some(3);
            let rax = u32::MAX;
            let max = u32::MAX;
            
            let res = incr(wrax, beta, degree, sub, lim, guess, rax, max);
            
            assert_eq!(None, res);
        }
        
        #[test]
        // essentially, same as beta_is_beta_test
        fn guess_is_beta_test1() {
            let wrax = 20;
            let beta = 3;
            let degree = 3;
            let sub = 67;
            let lim = 12100;
            let guess = Some(3);
            let rax = u32::MAX;
            let max = u32::MAX;
            
            let res = incr(wrax, beta, degree, sub, lim, guess, rax, max);
            
            assert_eq!(Some((23, 12100)), res);
        }
        
        #[test]
        fn guess_is_beta_test2() {
            let wrax = 20;
            let beta = 3;
            let degree = 3;
            let sub = 68;
            let lim = 12100;
            let guess = Some(3);
            let rax = u32::MAX;
            let max = u32::MAX;
            
            let res = incr(wrax, beta, degree, sub, lim, guess, rax, max);
            
            assert_eq!(Some((23, 12099)), res);
        }
        
        #[test]
        fn beta_too_much_test() {
            let wrax = 20;
            let beta = 1;
            let degree = 3;
            let sub = 60;
            let lim = 9200;
            let guess = None;
            let rax = u32::MAX - 1;
            let max = u32::MAX - 2;
            
            let res = incr(wrax, beta, degree, sub, lim, guess, rax, max);
            
            assert_eq!(Some((u32::MAX - 1, u32::MAX - 2)), res);
        }
        
        #[test]
        // essentially, same as guess_is_beta_test
        fn beta_is_beta_test1() {
            let wrax = 20;
            let beta = 3;
            let degree = 3;
            let sub = 67;
            let lim = 12100;
            let guess = None;
            let rax = u32::MAX;
            let max = u32::MAX;
            
            let res = incr(wrax, beta, degree, sub, lim, guess, rax, max);
            
            assert_eq!(Some((23, 12100)), res);
        }
        
        #[test]
        fn beta_is_beta_test2() {
            let wrax = 20;
            let beta = 3;
            let degree = 3;
            let sub = 68;
            let lim = 12100;
            let guess = None;
            let rax = u32::MAX;
            let max = u32::MAX;
            
            let res = incr(wrax, beta, degree, sub, lim, guess, rax, max);
            
            assert_eq!(Some((23, 12099)), res);
        }
    }
    
    mod decr {
        use super::super::decr;
        
        #[test]
        fn max_equal_lim_test() {
            let wrax = 20;
            let beta = 5;
            let degree = 4;
            let sub = 776;
            let lim = 331_000;
            
            let res = decr(wrax, beta, degree, sub, lim);
            assert_eq!((24, 331_000), res);
        }
        
        #[test]
        fn max_less_lim_test() {
            let wrax = 20;
            let beta = 5;
            let degree = 4;
            let sub = 777;
            let lim = 331_000;
            
            let res = decr(wrax, beta, degree, sub, lim);
            assert_eq!((24, 330_999), res);
        }
        
        #[test]
        fn subtracting_test() {
            let wrax = 20;
            let beta = 6;
            let degree = 4;
            let sub = 776;
            let lim = 331_000;
            
            let res = decr(wrax, beta, degree, sub, lim);
            assert_eq!((24, 331_000), res);
        }
    }

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

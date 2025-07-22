use std::cmp::max;

use super::{
    addition_sum, addition_two, divrem_accelerated, mulmul, pow_raw, rel_raw,
    subtraction_decremental, RawRow, Rel,
};

// task: think of shortcuts
// any root of 0 = 0
// any root of 1 = 1
// root 1 of any = any

#[cfg(test)]
use crate::tests_of_units::divrem_accelerated::TestGauges;

fn next(
    rax: &mut RawRow, // y
    rem: RawRow,      // r
    bdp: &RawRow,     // Bⁿ
    alpha: &RawRow,   // α
    degree: u16,      // n
    degree_less: u16, // n -1
    dbdlp: &RawRow,   // nBⁿ⁻¹
    unity: &RawRow,   // 1

    #[cfg(test)] wrax_out: &mut RawRow,
    #[cfg(test)] rax_pow_less_out: &mut RawRow,
    #[cfg(test)] sub_out: &mut RawRow,
    #[cfg(test)] lim_out: &mut RawRow,
    #[cfg(test)] div_out: &mut RawRow,
    #[cfg(test)] beta_out: &mut RawRow,
    #[cfg(test)] guess_out: &mut Option<RawRow>,
    #[cfg(test)] incr_out: &mut bool,
    #[cfg(test)] decr_out: &mut bool,
) -> RawRow {
    // yⁿ⁻¹
    let rax_pow_less = pow_raw(&rax, degree_less);

    // Bⁿyⁿ, subtrahend
    let sub = mulmul_incremental(bdp, mulmul(&rax_pow_less, &rax, 1), 1);

    // By, widen rax
    // expansion instead of multiplication
    if is_nought_raw(&rax) == false {
        // y' =By +β, β =0
        rax.insert(0, 0);
    }

    // Bⁿr +α, limit
    let mut lim = mulmul_incremental(bdp, rem, 1);
    addition_sum(alpha, &mut lim, 0);

    #[cfg(test)]
    {
        *rax_pow_less_out = rax_pow_less.clone();
    }

    // let make initial guess, if possible
    let (guess, mut beta) = if let Some(g) = guess(
        rax_pow_less,
        dbdlp,
        &lim,
        #[cfg(test)]
        div_out,
    ) {
        (Some(g.clone()), g)
    } else {
        (None, unity.clone())
    };

    #[cfg(test)]
    {
        *wrax_out = rax.clone();
        *sub_out = sub.clone();
        *lim_out = lim.clone();
        *beta_out = beta.clone();
        *guess_out = guess.clone();
    }

    let inc_res = incr(rax, &mut beta, unity, degree, &sub, &lim, &guess);

    // (By +β)ⁿ -Bⁿyⁿ
    let max = match inc_res {
        IncRes::Attainment((r, m)) => {
            #[cfg(test)]
            set_cr_out(incr_out);

            *rax = r;
            m
        }
        IncRes::MaxZero => {
            // (By +β)ⁿ -Bⁿyⁿ
            // β =0 =>(By)ⁿ -Bⁿyⁿ =0
            nought_raw()
        }
        IncRes::OverGuess(mut or) => {
            #[cfg(test)]
            set_cr_out(decr_out);

            let m = decr(&mut or, unity, degree, &sub, &lim);
            *rax = or;
            m
        }
    };

    // r' =(Bⁿr +α) -((By +β)ⁿ -Bⁿyⁿ)
    subtraction_decremental(
        &mut lim,
        &max,
        false,
        #[cfg(test)]
        &mut 0,
    );

    return lim;

    #[cfg(test)]
    fn set_cr_out(cr_out: &mut bool) {
        *cr_out = true;
    }
}

// task: test whether guess is really some benefit
// it is quite complex => misses can be cheaper
fn guess(
    rax_pow_less: RawRow,
    dbdlp: &RawRow,
    lim: &RawRow,
    #[cfg(test)] div_out: &mut RawRow,
) -> Option<RawRow> {
    if !is_nought_raw(rax_pow_less.as_slice()) {
        // nBⁿ⁻¹ ·yⁿ⁻¹
        let div = mulmul_incremental(dbdlp, rax_pow_less, 1);

        #[cfg(test)]
        {
            *div_out = div.clone();
        }

        // (Bⁿr +α) ÷(nBⁿ⁻¹ ·yⁿ⁻¹)
        let g = divrem_accelerated(
            lim,
            &div,
            #[cfg(test)]
            &mut TestGauges::blank(),
        )
        .1;

        if g.len() > 1 || g[0] > 1 {
            return Some(g);
        }
    }

    None
}

#[cfg_attr(test, derive(PartialEq, Debug))]
enum IncRes {
    OverGuess(RawRow),
    MaxZero,
    Attainment((RawRow, RawRow)),
}

fn incr<'a>(
    wrax: &RawRow,
    beta: &mut RawRow,
    unity: &RawRow,
    degree: u16,
    sub: &RawRow,
    lim: &RawRow,
    guess: &Option<RawRow>,
) -> IncRes {
    // seeking largest beta that
    // (By +β)ⁿ -Bⁿyⁿ ≤ Bⁿr +α

    let wrax_len = wrax.len();
    let beta_len = beta.len();
    let max_len = max(wrax_len, beta_len);

    let mut orax = Vec::with_capacity(max_len + 1);

    // o stands for operative
    // y' =By +β
    addition_two(beta, &wrax, &mut orax);
    let mut init_fail = true;

    let mut max = Vec::new();

    loop {
        // (By +β)ⁿ
        let mut omax = pow_raw(&orax, degree);

        // (By +β)ⁿ -Bⁿyⁿ
        subtraction_decremental(
            &mut omax,
            sub,
            false,
            #[cfg(test)]
            &mut 0,
        );

        // (By +β)ⁿ -Bⁿyⁿ ≤ Bⁿr +α
        if let Rel::Greater(_) = rel_raw(&omax, lim) {
            if init_fail {
                return if guess.is_some() {
                    IncRes::OverGuess(orax)
                } else {
                    IncRes::MaxZero
                };
            }

            subtraction_decremental(
                &mut orax,
                unity,
                false,
                #[cfg(test)]
                &mut 0,
            );

            return IncRes::Attainment((orax, max));
        }

        // (By +β)ⁿ -Bⁿyⁿ ≤ Bⁿr +α
        if Rel::Equal == rel_raw(&omax, lim) {
            return IncRes::Attainment((orax, omax));
        }

        init_fail = false;
        max = omax;

        addition_sum(unity, &mut orax, 0);
    }
}

// do not decrement beta and add to wrax each iteration
// add first than decrement orax
fn decr(orax: &mut RawRow, unity: &RawRow, degree: u16, sub: &RawRow, lim: &RawRow) -> RawRow {
    // seeking largest beta that
    // (By +β)ⁿ -Bⁿyⁿ ≤ Bⁿr +α
    loop {
        _ = subtraction_decremental(
            orax,
            unity,
            false,
            #[cfg(test)]
            &mut 0,
        );

        // (By +β)ⁿ
        let mut omax = pow_raw(&orax, degree);

        // (By +β)ⁿ -Bⁿyⁿ
        subtraction_decremental(
            &mut omax,
            sub,
            false,
            #[cfg(test)]
            &mut 0,
        );

        // (By +β)ⁿ -Bⁿyⁿ ≤ Bⁿr +α
        if let Rel::Greater(_) = rel_raw(&omax, lim) {
            continue;
        }

        return omax;
    }
}

// Let α be the next n digits of the radicand.
pub struct AlphaGenerator<'a> {
    // operative number
    onum: &'a [u8],
    // slice index
    ix: usize,
    // radix size
    ras: usize,
    // zero
    ngh: RawRow,
}

use crate::{is_nought_raw, mulmul_incremental, nought_raw};
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
            onum: num,
            ras,
            ix,
            ngh: nought_raw(),
        }
    }

    pub fn next(&mut self) -> &[u8] {
        let onum = self.onum;

        if onum.len() == 0 {
            return &self.ngh;
        }

        let ix = self.ix;
        let alpha = &onum[ix..];
        self.onum = &onum[..ix];

        if ix > 0 {
            self.ix = ix - self.ras;
        }

        return alpha;
    }
}

#[cfg(test)]
mod tests_of_units {

    mod next {
        use crate::{unity_raw, Row};

        use super::super::next;

        #[test]
        fn basic_test() {
            let mut rax_ref = new_from_num!(3).row;
            let mut rem_ref = new_from_num!(15).row;
            let bdp = new_from_num!(1000).row;
            let alpha = new_from_num!(133).row;
            let degree = 3;
            let degree_less = 2;
            let dbdlp = new_from_num!(300).row;
            let unity = unity_raw();

            let empty_out = new_from_num!(u32::MAX).row;
            let mut wrax_out = empty_out.clone();
            let mut rax_pow_less_out = empty_out.clone();
            let mut sub_out = empty_out.clone();
            let mut lim_out = empty_out.clone();
            let mut div_out = empty_out.clone();
            let mut beta_out = empty_out.clone();
            let mut guess_out = Some(empty_out.clone());

            rem_ref = next(
                &mut rax_ref,
                rem_ref,
                &bdp,
                &alpha,
                degree,
                degree_less,
                &dbdlp,
                &unity,
                &mut wrax_out,
                &mut rax_pow_less_out,
                &mut sub_out,
                &mut lim_out,
                &mut div_out,
                &mut beta_out,
                &mut guess_out,
                &mut false,
                &mut false,
            );

            let sub = 27_000;
            let lim = 15_133;
            let div = 2700;

            let beta = lim / div;
            let rem = lim - (34u32.pow(degree as u32) - sub);

            let sub = new_from_num!(sub).row;
            let lim = new_from_num!(lim).row;
            let div = new_from_num!(div).row;

            let beta = new_from_num!(beta).row;
            let rem = new_from_num!(rem).row;

            assert_eq!(vec![0, 3], wrax_out);
            assert_eq!(vec![9], rax_pow_less_out);
            assert_eq!(sub, sub_out);
            assert_eq!(lim, lim_out);
            assert_eq!(div, div_out);

            assert_eq!(beta, beta_out);
            assert_eq!(Some(beta), guess_out);

            assert_eq!(vec![4, 3], rax_ref);
            assert_eq!(rem, rem_ref);
        }

        #[test]
        fn rax_zero_test() {
            let mut rax_ref = new_from_num!(0).row;
            let rem_ref = new_from_num!(0).row;
            let bdp = new_from_num!(1000).row;
            let alpha = new_from_num!(133).row;
            let degree = 3;
            let degree_less = 2;
            let dbdlp = new_from_num!(300).row;
            let unity = unity_raw();

            let empty_out = new_from_num!(u32::MAX).row;
            let mut wrax_out = empty_out.clone();
            let mut rax_pow_less_out = empty_out.clone();
            let mut sub_out = empty_out.clone();
            let mut lim_out = empty_out.clone();
            let mut div_out = empty_out.clone();
            let mut beta_out = empty_out.clone();
            let mut guess_out = Some(empty_out.clone());

            _ = next(
                &mut rax_ref,
                rem_ref,
                &bdp,
                &alpha,
                degree,
                degree_less,
                &dbdlp,
                &unity,
                &mut wrax_out,
                &mut rax_pow_less_out,
                &mut sub_out,
                &mut lim_out,
                &mut div_out,
                &mut beta_out,
                &mut guess_out,
                &mut false,
                &mut false,
            );

            assert_eq!(vec![0], wrax_out);
            assert_eq!(vec![0], rax_pow_less_out);
            assert_eq!(vec![0], sub_out);
            assert_eq!(vec![3, 3, 1], lim_out);
            assert_eq!(empty_out, div_out);
            assert_eq!(vec![1], beta_out);
            assert_eq!(None, guess_out);
        }

        #[test]
        fn degree_one_test() {
            let mut rax_ref = new_from_num!(2).row;
            let rem_ref = new_from_num!(3).row;
            let bdp = new_from_num!(10).row;
            let alpha = new_from_num!(222).row;
            let degree = 1;
            let degree_less = 0;
            let dbdlp = new_from_num!(1).row;
            let unity = unity_raw();

            let empty_out = new_from_num!(u32::MAX).row;
            let mut wrax_out = empty_out.clone();
            let mut rax_pow_less_out = empty_out.clone();
            let mut sub_out = empty_out.clone();
            let mut lim_out = empty_out.clone();
            let mut div_out = empty_out.clone();
            let mut beta_out = empty_out.clone();
            let mut guess_out = Some(empty_out.clone());

            _ = next(
                &mut rax_ref,
                rem_ref,
                &bdp,
                &alpha,
                degree,
                degree_less,
                &dbdlp,
                &unity,
                &mut wrax_out,
                &mut rax_pow_less_out,
                &mut sub_out,
                &mut lim_out,
                &mut div_out,
                &mut beta_out,
                &mut guess_out,
                &mut false,
                &mut false,
            );

            assert_eq!(vec![0, 2], wrax_out);
            assert_eq!(vec![1], rax_pow_less_out);
            assert_eq!(vec![0, 2], sub_out);
            assert_eq!(vec![2, 5, 2], lim_out);
            assert_eq!(vec![1], div_out);
            assert_eq!(vec![2, 5, 2], beta_out);
            assert_eq!(Some(vec![2, 5, 2]), guess_out);
        }

        #[test]
        fn g_zero_test() {
            let mut rax_ref = new_from_num!(2).row;
            let rem_ref = new_from_num!(1).row;
            let bdp = new_from_num!(1000).row;
            let alpha = new_from_num!(199).row;
            let degree = 3;
            let degree_less = 2;
            let dbdlp = new_from_num!(300).row;
            let unity = unity_raw();

            let empty_out = new_from_num!(u32::MAX).row;
            let mut wrax_out = empty_out.clone();
            let mut rax_pow_less_out = empty_out.clone();
            let mut sub_out = empty_out.clone();
            let mut lim_out = empty_out.clone();
            let mut div_out = empty_out.clone();
            let mut beta_out = empty_out.clone();
            let mut guess_out = Some(empty_out.clone());

            _ = next(
                &mut rax_ref,
                rem_ref,
                &bdp,
                &alpha,
                degree,
                degree_less,
                &dbdlp,
                &unity,
                &mut wrax_out,
                &mut rax_pow_less_out,
                &mut sub_out,
                &mut lim_out,
                &mut div_out,
                &mut beta_out,
                &mut guess_out,
                &mut false,
                &mut false,
            );

            assert_eq!(vec![0, 2], wrax_out);
            assert_eq!(vec![4], rax_pow_less_out);
            assert_eq!(vec![0, 0, 0, 8], sub_out);
            assert_eq!(vec![9, 9, 1, 1], lim_out);
            assert_eq!(vec![0, 0, 2, 1], div_out);
            assert_eq!(vec![1], beta_out);
            assert_eq!(None, guess_out);
        }

        #[test]
        fn g_one_test() {
            let mut rax_ref = new_from_num!(2).row;
            let rem_ref = new_from_num!(2).row;
            let bdp = new_from_num!(1000).row;
            let alpha = new_from_num!(399).row;
            let degree = 3;
            let degree_less = 2;
            let dbdlp = new_from_num!(300).row;
            let unity = unity_raw();

            let empty_out = new_from_num!(u32::MAX).row;
            let mut wrax_out = empty_out.clone();
            let mut rax_pow_less_out = empty_out.clone();
            let mut sub_out = empty_out.clone();
            let mut lim_out = empty_out.clone();
            let mut div_out = empty_out.clone();
            let mut beta_out = empty_out.clone();
            let mut guess_out = Some(empty_out.clone());

            _ = next(
                &mut rax_ref,
                rem_ref,
                &bdp,
                &alpha,
                degree,
                degree_less,
                &dbdlp,
                &unity,
                &mut wrax_out,
                &mut rax_pow_less_out,
                &mut sub_out,
                &mut lim_out,
                &mut div_out,
                &mut beta_out,
                &mut guess_out,
                &mut false,
                &mut false,
            );

            assert_eq!(vec![0, 2], wrax_out);
            assert_eq!(vec![4], rax_pow_less_out);
            assert_eq!(vec![0, 0, 0, 8], sub_out);
            assert_eq!(vec![9, 9, 3, 2], lim_out);
            assert_eq!(vec![0, 0, 2, 1], div_out);
            assert_eq!(vec![1], beta_out);
            assert_eq!(None, guess_out);
        }

        #[test]
        fn g_two_test() {
            let mut rax_ref = new_from_num!(2).row;
            let rem_ref = new_from_num!(2).row;
            let bdp = new_from_num!(1000).row;
            let alpha = new_from_num!(400).row;
            let degree = 3;
            let degree_less = 2;
            let dbdlp = new_from_num!(300).row;
            let unity = unity_raw();

            let empty_out = new_from_num!(u32::MAX).row;
            let mut wrax_out = empty_out.clone();
            let mut rax_pow_less_out = empty_out.clone();
            let mut sub_out = empty_out.clone();
            let mut lim_out = empty_out.clone();
            let mut div_out = empty_out.clone();
            let mut beta_out = empty_out.clone();
            let mut guess_out = Some(empty_out.clone());

            _ = next(
                &mut rax_ref,
                rem_ref,
                &bdp,
                &alpha,
                degree,
                degree_less,
                &dbdlp,
                &unity,
                &mut wrax_out,
                &mut rax_pow_less_out,
                &mut sub_out,
                &mut lim_out,
                &mut div_out,
                &mut beta_out,
                &mut guess_out,
                &mut false,
                &mut false,
            );

            assert_eq!(vec![0, 2], wrax_out);
            assert_eq!(vec![4], rax_pow_less_out);
            assert_eq!(vec![0, 0, 0, 8], sub_out);
            assert_eq!(vec![0, 0, 4, 2], lim_out);
            assert_eq!(vec![0, 0, 2, 1], div_out);
            assert_eq!(vec![2], beta_out);
            assert_eq!(Some(vec![2]), guess_out);
        }

        #[test]
        fn incr_test() {
            let mut rax_ref = new_from_num!(3).row;
            let rem_ref = new_from_num!(4).row;
            let bdp = new_from_num!(1000).row;
            let alpha = new_from_num!(133).row;
            let degree = 3;
            let degree_less = 2;
            let dbdlp = new_from_num!(300).row;
            let unity = unity_raw();

            let empty_out = new_from_num!(u32::MAX).row;
            let mut wrax_out = empty_out.clone();
            let mut rax_pow_less_out = empty_out.clone();
            let mut sub_out = empty_out.clone();
            let mut lim_out = empty_out.clone();
            let mut div_out = empty_out.clone();
            let mut beta_out = empty_out.clone();
            let mut guess_out = Some(empty_out.clone());
            let mut incr_out = false;
            let mut decr_out = false;

            _ = next(
                &mut rax_ref,
                rem_ref,
                &bdp,
                &alpha,
                degree,
                degree_less,
                &dbdlp,
                &unity,
                &mut wrax_out,
                &mut rax_pow_less_out,
                &mut sub_out,
                &mut lim_out,
                &mut div_out,
                &mut beta_out,
                &mut guess_out,
                &mut incr_out,
                &mut decr_out,
            );

            assert_eq!(true, incr_out);
            assert_eq!(false, decr_out);
        }

        #[test]
        fn decr_test() {
            let mut rax_ref = new_from_num!(3).row;
            let rem_ref = new_from_num!(15).row;
            let bdp = new_from_num!(1000).row;
            let alpha = new_from_num!(133).row;
            let degree = 3;
            let degree_less = 2;
            let dbdlp = new_from_num!(300).row;
            let unity = unity_raw();

            let empty_out = new_from_num!(u32::MAX).row;
            let mut wrax_out = empty_out.clone();
            let mut rax_pow_less_out = empty_out.clone();
            let mut sub_out = empty_out.clone();
            let mut lim_out = empty_out.clone();
            let mut div_out = empty_out.clone();
            let mut beta_out = empty_out.clone();
            let mut guess_out = Some(empty_out.clone());
            let mut incr_out = false;
            let mut decr_out = false;

            _ = next(
                &mut rax_ref,
                rem_ref,
                &bdp,
                &alpha,
                degree,
                degree_less,
                &dbdlp,
                &unity,
                &mut wrax_out,
                &mut rax_pow_less_out,
                &mut sub_out,
                &mut lim_out,
                &mut div_out,
                &mut beta_out,
                &mut guess_out,
                &mut incr_out,
                &mut decr_out,
            );

            assert_eq!(false, incr_out);
            assert_eq!(true, decr_out);
        }
    }

    mod incr {
        use crate::nth_root::{incr, IncRes};
        use crate::{unity_raw, Row};

        #[test]
        fn guess_too_much_test() {
            let wrax = new_from_num!(20).row;
            let mut beta = new_from_num!(3).row;
            let unity = unity_raw();
            let degree = 3;
            let sub = new_from_num!(66).row;
            let lim = new_from_num!(12100).row;
            let guess = Some(new_from_num!(3).row);

            let res = incr(&wrax, &mut beta, &unity, degree, &sub, &lim, &guess);

            let orax = new_from_num!(23).row;
            assert_eq!(IncRes::OverGuess(orax), res);
        }

        #[test]
        // essentially, same as beta_is_beta_test
        fn guess_is_beta_test1() {
            let wrax = new_from_num!(20).row;
            let mut beta = new_from_num!(3).row;
            let unity = unity_raw();
            let degree = 3;
            let sub = new_from_num!(67).row;
            let lim = new_from_num!(12100).row;
            let guess = Some(new_from_num!(3).row);

            let res = incr(&wrax, &mut beta, &unity, degree, &sub, &lim, &guess);

            let rax = new_from_num!(23).row;
            let max = new_from_num!(12100).row;

            assert_eq!(IncRes::Attainment((rax, max)), res);
        }

        #[test]
        fn guess_is_beta_test2() {
            let wrax = new_from_num!(20).row;
            let mut beta = new_from_num!(3).row;
            let unity = unity_raw();
            let degree = 3;
            let sub = new_from_num!(68).row;
            let lim = new_from_num!(12100).row;
            let guess = Some(new_from_num!(3).row);

            let res = incr(&wrax, &mut beta, &unity, degree, &sub, &lim, &guess);

            let rax = new_from_num!(23).row;
            let max = new_from_num!(12099).row;

            assert_eq!(IncRes::Attainment((rax, max)), res);
        }

        #[test]
        fn beta_too_much_test() {
            let wrax = new_from_num!(20).row;
            let mut beta = new_from_num!(1).row;
            let unity = unity_raw();
            let degree = 3;
            let sub = new_from_num!(60).row;
            let lim = new_from_num!(9200).row;
            let guess = None;

            let res = incr(&wrax, &mut beta, &unity, degree, &sub, &lim, &guess);

            assert_eq!(IncRes::MaxZero, res);
        }

        #[test]
        // essentially, same as guess_is_beta_test
        fn beta_is_beta_test1() {
            let wrax = new_from_num!(20).row;
            let mut beta = new_from_num!(3).row;
            let unity = unity_raw();
            let degree = 3;
            let sub = new_from_num!(67).row;
            let lim = new_from_num!(12100).row;
            let guess = None;

            let res = incr(&wrax, &mut beta, &unity, degree, &sub, &lim, &guess);

            let rax = new_from_num!(23).row;
            let max = new_from_num!(12100).row;

            assert_eq!(IncRes::Attainment((rax, max)), res);
        }

        #[test]
        fn beta_is_beta_test2() {
            let wrax = new_from_num!(20).row;
            let mut beta = new_from_num!(3).row;
            let unity = unity_raw();
            let degree = 3;
            let sub = new_from_num!(68).row;
            let lim = new_from_num!(12100).row;
            let guess = None;

            let res = incr(&wrax, &mut beta, &unity, degree, &sub, &lim, &guess);

            let rax = new_from_num!(23).row;
            let max = new_from_num!(12099).row;

            assert_eq!(IncRes::Attainment((rax, max)), res);
        }
    }

    mod decr {
        use crate::{unity_raw, Row};

        use super::super::decr;

        #[test]
        fn max_equal_lim_test() {
            let mut orax = new_from_num!(25).row;
            let unity = unity_raw();
            let degree = 4;
            let sub = new_from_num!(776).row;
            let lim = new_from_num!(331_000).row;

            let omax = decr(&mut orax, &unity, degree, &sub, &lim);

            let rax = new_from_num!(24).row;
            let max = new_from_num!(331_000).row;

            assert_eq!(rax, orax);
            assert_eq!(max, omax);
        }

        #[test]
        fn max_less_lim_test() {
            let mut orax = new_from_num!(25).row;
            let unity = unity_raw();
            let degree = 4;
            let sub = new_from_num!(777).row;
            let lim = new_from_num!(331_000).row;

            let omax = decr(&mut orax, &unity, degree, &sub, &lim);

            let rax = new_from_num!(24).row;
            let max = new_from_num!(330_999).row;

            assert_eq!(rax, orax);
            assert_eq!(max, omax);
        }

        #[test]
        fn subtracting_test() {
            let mut orax = new_from_num!(26).row;
            let unity = unity_raw();
            let degree = 4;
            let sub = new_from_num!(776).row;
            let lim = new_from_num!(331_000).row;

            let omax = decr(&mut orax, &unity, degree, &sub, &lim);

            let rax = new_from_num!(24).row;
            let max = new_from_num!(331_000).row;

            assert_eq!(rax, orax);
            assert_eq!(max, omax);
        }
    }

    mod alpha_generator {
        use super::super::AlphaGenerator;

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

// cargo fmt & cargo test --release nth_root

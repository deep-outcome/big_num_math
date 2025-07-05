use std::cmp::max;

use super::{
    addition_sum, addition_two, divrem_accelerated, mulmul, pow_raw, rel_raw, subtraction,
    subtraction_decremental, RawRow, Rel,
};

// think of shortcuts
// any root of 0 = 0
// any root of 1 = 1
// root 1 of any = any

#[cfg(test)]
use crate::tests_of_units::divrem_accelerated::TestGauges;

fn next(
    rax: &mut RawRow, // y
    rem: &mut RawRow, // r
    bdp: &RawRow,     // Bⁿ
    alpha: &RawRow,   // α
    degree: u16,      // n
    degree_less: u16, // n -1
    dbdlp: &RawRow,   // nBⁿ⁻¹
    unity: &RawRow,   // 1
    lim: &mut RawRow,

    #[cfg(test)] wrax_out: &mut RawRow,
    #[cfg(test)] rax_pow_less_out: &mut RawRow,
    #[cfg(test)] sub_out: &mut RawRow,
    #[cfg(test)] lim_out: &mut RawRow,
    #[cfg(test)] div_out: &mut RawRow,
    #[cfg(test)] beta_out: &mut RawRow,
    #[cfg(test)] guess_out: &mut Option<RawRow>,
    #[cfg(test)] incr_out: &mut bool,
    #[cfg(test)] decr_out: &mut bool,
) {
    // By, widen rax
    // extended cloning instead of multiplication
    let mut wrax = if is_nought_raw(rax) {
        nought_raw()
    } else {
        let wrax_len = rax.len() + 1;
        let mut wrax = Vec::with_capacity(wrax_len);

        let sc = wrax.spare_capacity_mut();
        // ⋅B
        sc[0].write(0);

        let mut ix = 1;
        while ix < wrax_len {
            sc[ix].write(rax[ix - 1]);
            ix += 1;
        }

        unsafe {
            wrax.set_len(wrax_len);
        }

        wrax
    };

    // yⁿ⁻¹
    let rax_pow_less = pow_raw(rax, degree_less);

    // Bⁿyⁿ, subtrahend
    let sub = mulmul(bdp, &mulmul(&rax_pow_less, rax, 1), 1);

    // Bⁿr +α, limit
    lim.clear();
    addition_two(&mulmul(bdp, rem, 1), alpha, lim);

    // let make initial guess, if possible
    let (guess, mut beta) = if let Some(g) = guess(
        &rax_pow_less,
        dbdlp,
        lim,
        #[cfg(test)]
        div_out,
    ) {
        (Some(g.clone()), g)
    } else {
        (None, unity.clone())
    };

    #[cfg(test)]
    {
        *wrax_out = wrax.clone();
        *rax_pow_less_out = rax_pow_less.clone();
        *sub_out = sub.clone();
        *lim_out = lim.clone();
        *beta_out = beta.clone();
        *guess_out = guess.clone();
    }

    // (By +β)ⁿ -Bⁿyⁿ
    let max;
    let inc_res = incr(&wrax, &mut beta, unity, degree, &sub, lim, &guess);

    if let Some((r, m)) = inc_res {
        #[cfg(test)]
        {
            *incr_out = true;
        }

        *rax = r;
        max = m;
    } else {
        #[cfg(test)]
        {
            *decr_out = true;
        }

        max = decr(&mut wrax, &beta, unity, degree, &sub, &lim);
        *rax = wrax;
    }

    // r' =(Bⁿr +α) -((By +β)ⁿ -Bⁿyⁿ)
    *rem = subtraction(
        &lim,
        &max,
        false,
        #[cfg(test)]
        &mut 0,
    )
    .0;
}

fn guess(
    rax_pow_less: &RawRow,
    dbdlp: &RawRow,
    lim: &RawRow,
    #[cfg(test)] div_out: &mut RawRow,
) -> Option<RawRow> {
    if !is_nought_raw(rax_pow_less) {
        // nBⁿ⁻¹ ·yⁿ⁻¹
        let div = mulmul(dbdlp, &rax_pow_less, 1);

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

fn incr<'a>(
    wrax: &RawRow,
    beta: &mut RawRow,
    unity: &RawRow,
    degree: u16,
    sub: &RawRow,
    lim: &RawRow,
    guess: &Option<RawRow>,
) -> Option<(RawRow, RawRow)> {
    // seeking largest beta that
    // (By +β)ⁿ -Bⁿyⁿ ≤ Bⁿr +α

    // o stands for operative
    let wrax_len = wrax.len();
    let beta_len = beta.len();
    let max_len = max(wrax_len, beta_len);

    let mut orax = Vec::with_capacity(max_len + 1);

    // (By +β)ⁿ -Bⁿyⁿ
    // β =0 =>(By)ⁿ -Bⁿyⁿ =0
    let mut max = nought_raw();

    // y' =By +β, β =0
    let mut rax = wrax.clone();

    loop {
        // y' =By +β
        // let orax = wrax + beta;
        addition_two(wrax, &beta, &mut orax);

        // (By +β)ⁿ
        let orax_deg_pow = pow_raw(&orax, degree);

        // (By +β)ⁿ -Bⁿyⁿ
        // let omax = orax_deg_pow - sub;
        let omax = subtraction(
            &orax_deg_pow,
            sub,
            false,
            #[cfg(test)]
            &mut 0,
        )
        .0;

        // (By +β)ⁿ -Bⁿyⁿ ≤ Bⁿr +α
        // if omax > lim {
        if let Rel::Greater(_) = rel_raw(&omax, lim) {
            if let Some(g) = guess {
                if Rel::Equal == rel_raw(g, &beta) {
                    return None;
                }
            }

            break;
        }

        std::mem::swap(&mut orax, &mut rax);
        orax.clear();

        max = omax;

        // (By +β)ⁿ -Bⁿyⁿ ≤ Bⁿr +α
        // if omax == lim {
        if Rel::Equal == rel_raw(&max, lim) {
            break;
        }

        addition_sum(unity, beta, 0);
    }

    return Some((rax, max));
}

// do not decrement beta and add to wrax each iteration
// add first than decrement orax
fn decr(
    orax: &mut RawRow,
    beta: &RawRow,
    unity: &RawRow,
    degree: u16,
    sub: &RawRow,
    lim: &RawRow,
) -> RawRow {
    // y' =By +β
    //let orax = wrax + beta;
    addition_sum(&beta, orax, 0);

    // seeking largest beta that
    // (By +β)ⁿ -Bⁿyⁿ ≤ Bⁿr +α

    loop {
        // o stands for operative
        // beta -= 1;
        _ = subtraction_decremental(
            orax,
            unity,
            false,
            #[cfg(test)]
            &mut 0,
        );

        // (By +β)ⁿ
        // let orax_deg_pow = orax.pow(degree);
        let orax_deg_pow = pow_raw(&orax, degree);

        // (By +β)ⁿ -Bⁿyⁿ
        // let omax = orax_deg_pow - sub;
        let omax = subtraction(
            &orax_deg_pow,
            sub,
            false,
            #[cfg(test)]
            &mut 0,
        )
        .0;

        // (By +β)ⁿ -Bⁿyⁿ ≤ Bⁿr +α
        // if omax <= lim {

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

use crate::{is_nought_raw, nought_raw};
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
            let mut lim = vec![];

            let empty_out = new_from_num!(u32::MAX).row;
            let mut wrax_out = empty_out.clone();
            let mut rax_pow_less_out = empty_out.clone();
            let mut sub_out = empty_out.clone();
            let mut lim_out = empty_out.clone();
            let mut div_out = empty_out.clone();
            let mut beta_out = empty_out.clone();
            let mut guess_out = Some(empty_out.clone());

            next(
                &mut rax_ref,
                &mut rem_ref,
                &bdp,
                &alpha,
                degree,
                degree_less,
                &dbdlp,
                &unity,
                &mut lim,
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
            let mut rem_ref = new_from_num!(0).row;
            let bdp = new_from_num!(1000).row;
            let alpha = new_from_num!(133).row;
            let degree = 3;
            let degree_less = 2;
            let dbdlp = new_from_num!(300).row;
            let unity = unity_raw();
            let mut lim = vec![];

            let empty_out = new_from_num!(u32::MAX).row;
            let mut wrax_out = empty_out.clone();
            let mut rax_pow_less_out = empty_out.clone();
            let mut sub_out = empty_out.clone();
            let mut lim_out = empty_out.clone();
            let mut div_out = empty_out.clone();
            let mut beta_out = empty_out.clone();
            let mut guess_out = Some(empty_out.clone());

            next(
                &mut rax_ref,
                &mut rem_ref,
                &bdp,
                &alpha,
                degree,
                degree_less,
                &dbdlp,
                &unity,
                &mut lim,
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
            let mut rem_ref = new_from_num!(3).row;
            let bdp = new_from_num!(10).row;
            let alpha = new_from_num!(222).row;
            let degree = 1;
            let degree_less = 0;
            let dbdlp = new_from_num!(1).row;
            let unity = unity_raw();
            let mut lim = vec![];

            let empty_out = new_from_num!(u32::MAX).row;
            let mut wrax_out = empty_out.clone();
            let mut rax_pow_less_out = empty_out.clone();
            let mut sub_out = empty_out.clone();
            let mut lim_out = empty_out.clone();
            let mut div_out = empty_out.clone();
            let mut beta_out = empty_out.clone();
            let mut guess_out = Some(empty_out.clone());

            next(
                &mut rax_ref,
                &mut rem_ref,
                &bdp,
                &alpha,
                degree,
                degree_less,
                &dbdlp,
                &unity,
                &mut lim,
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
            let mut rem_ref = new_from_num!(1).row;
            let bdp = new_from_num!(1000).row;
            let alpha = new_from_num!(199).row;
            let degree = 3;
            let degree_less = 2;
            let dbdlp = new_from_num!(300).row;
            let unity = unity_raw();
            let mut lim = vec![];

            let empty_out = new_from_num!(u32::MAX).row;
            let mut wrax_out = empty_out.clone();
            let mut rax_pow_less_out = empty_out.clone();
            let mut sub_out = empty_out.clone();
            let mut lim_out = empty_out.clone();
            let mut div_out = empty_out.clone();
            let mut beta_out = empty_out.clone();
            let mut guess_out = Some(empty_out.clone());

            next(
                &mut rax_ref,
                &mut rem_ref,
                &bdp,
                &alpha,
                degree,
                degree_less,
                &dbdlp,
                &unity,
                &mut lim,
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
            let mut rem_ref = new_from_num!(2).row;
            let bdp = new_from_num!(1000).row;
            let alpha = new_from_num!(399).row;
            let degree = 3;
            let degree_less = 2;
            let dbdlp = new_from_num!(300).row;
            let unity = unity_raw();
            let mut lim = vec![];

            let empty_out = new_from_num!(u32::MAX).row;
            let mut wrax_out = empty_out.clone();
            let mut rax_pow_less_out = empty_out.clone();
            let mut sub_out = empty_out.clone();
            let mut lim_out = empty_out.clone();
            let mut div_out = empty_out.clone();
            let mut beta_out = empty_out.clone();
            let mut guess_out = Some(empty_out.clone());

            next(
                &mut rax_ref,
                &mut rem_ref,
                &bdp,
                &alpha,
                degree,
                degree_less,
                &dbdlp,
                &unity,
                &mut lim,
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
            let mut rem_ref = new_from_num!(2).row;
            let bdp = new_from_num!(1000).row;
            let alpha = new_from_num!(400).row;
            let degree = 3;
            let degree_less = 2;
            let dbdlp = new_from_num!(300).row;
            let unity = unity_raw();
            let mut lim = vec![];

            let empty_out = new_from_num!(u32::MAX).row;
            let mut wrax_out = empty_out.clone();
            let mut rax_pow_less_out = empty_out.clone();
            let mut sub_out = empty_out.clone();
            let mut lim_out = empty_out.clone();
            let mut div_out = empty_out.clone();
            let mut beta_out = empty_out.clone();
            let mut guess_out = Some(empty_out.clone());

            next(
                &mut rax_ref,
                &mut rem_ref,
                &bdp,
                &alpha,
                degree,
                degree_less,
                &dbdlp,
                &unity,
                &mut lim,
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
            let mut rem_ref = new_from_num!(4).row;
            let bdp = new_from_num!(1000).row;
            let alpha = new_from_num!(133).row;
            let degree = 3;
            let degree_less = 2;
            let dbdlp = new_from_num!(300).row;
            let unity = unity_raw();
            let mut lim = vec![];

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

            next(
                &mut rax_ref,
                &mut rem_ref,
                &bdp,
                &alpha,
                degree,
                degree_less,
                &dbdlp,
                &unity,
                &mut lim,
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
            let mut rem_ref = new_from_num!(15).row;
            let bdp = new_from_num!(1000).row;
            let alpha = new_from_num!(133).row;
            let degree = 3;
            let degree_less = 2;
            let dbdlp = new_from_num!(300).row;
            let unity = unity_raw();
            let mut lim = vec![];

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

            next(
                &mut rax_ref,
                &mut rem_ref,
                &bdp,
                &alpha,
                degree,
                degree_less,
                &dbdlp,
                &unity,
                &mut lim,
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
        use super::super::incr;
        use crate::{nought_raw, unity_raw, Row};

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

            assert_eq!(None, res);
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

            assert_eq!(Some((rax, max)), res);
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

            assert_eq!(Some((rax, max)), res);
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

            let rax = wrax;
            let max = nought_raw();

            assert_eq!(Some((rax, max)), res);
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

            assert_eq!(Some((rax, max)), res);
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

            assert_eq!(Some((rax, max)), res);
        }
    }

    mod decr {
        use crate::{unity_raw, Row};

        use super::super::decr;

        #[test]
        fn max_equal_lim_test() {
            let mut orax = new_from_num!(20).row;
            let beta = new_from_num!(5).row;
            let unity = unity_raw();
            let degree = 4;
            let sub = new_from_num!(776).row;
            let lim = new_from_num!(331_000).row;

            let omax = decr(&mut orax, &beta, &unity, degree, &sub, &lim);

            let rax = new_from_num!(24).row;
            let max = new_from_num!(331_000).row;

            assert_eq!(rax, orax);
            assert_eq!(max, omax);
        }

        #[test]
        fn max_less_lim_test() {
            let mut orax = new_from_num!(20).row;
            let beta = new_from_num!(5).row;
            let unity = unity_raw();
            let degree = 4;
            let sub = new_from_num!(777).row;
            let lim = new_from_num!(331_000).row;

            let omax = decr(&mut orax, &beta, &unity, degree, &sub, &lim);

            let rax = new_from_num!(24).row;
            let max = new_from_num!(330_999).row;

            assert_eq!(rax, orax);
            assert_eq!(max, omax);
        }

        #[test]
        fn subtracting_test() {
            let mut orax = new_from_num!(20).row;
            let beta = new_from_num!(6).row;
            let unity = unity_raw();
            let degree = 4;
            let sub = new_from_num!(776).row;
            let lim = new_from_num!(331_000).row;

            let omax = decr(&mut orax, &beta, &unity, degree, &sub, &lim);

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

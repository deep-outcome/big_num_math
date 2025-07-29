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

#[cfg(test)]
use tests_of_units::next::test_aides::TestOuts;

fn next(
    rax: &mut RawRow, // y
    rem: RawRow,      // r
    bdp: &RawRow,     // Bⁿ
    alpha: &RawRow,   // α
    degree: u16,      // n
    degree_less: u16, // n -1
    dbdlp: &RawRow,   // nBⁿ⁻¹
    unity: &RawRow,   // 1

    #[cfg(test)] outs: &mut TestOuts,
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
        outs.rax_pow_less = rax_pow_less.clone();
    }

    // let make initial guess, if possible
    let (betag, beta) = if let Some(g) = guess(
        rax_pow_less,
        dbdlp,
        &lim,
        #[cfg(test)]
        &mut outs.div,
        #[cfg(test)]
        &mut vec![],
    ) {
        (true, g)
    } else {
        (false, unity.clone())
    };

    #[cfg(test)]
    {
        outs.wrax = rax.clone();
        outs.sub = sub.clone();
        outs.lim = lim.clone();
        outs.beta = beta.clone();
        outs.betag = Some(betag);
    }

    let inc_res = incr(rax, &beta, unity, degree, &sub, &lim, betag);

    // (By +β)ⁿ -Bⁿyⁿ
    let max = match inc_res {
        IncRes::Attainment((r, m)) => {
            #[cfg(test)]
            set_cr(&mut outs.incr);

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
            set_cr(&mut outs.decr);

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
    fn set_cr(cr: &mut bool) {
        *cr = true;
    }
}

// task: test whether guess is really some benefit
// it is quite complex => misses can be cheaper
fn guess(
    rax_pow_less: RawRow,
    dbdlp: &RawRow,
    lim: &RawRow,
    #[cfg(test)] div_out: &mut RawRow,
    #[cfg(test)] g_out: &mut RawRow,
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

        #[cfg(test)]
        {
            *g_out = g.clone();
        }

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
    beta: &RawRow,
    unity: &RawRow,
    degree: u16,
    sub: &RawRow,
    lim: &RawRow,
    betag: bool,
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

    let mut max = Vec::with_capacity(0);

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
        let rel = rel_raw(&omax, lim);
        if let Rel::Greater(_) = rel {
            if init_fail {
                return if betag {
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
        if Rel::Equal == rel {
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

    pub mod next {

        pub mod test_aides {
            use crate::{RawRow, Row};

            pub struct TestSet {
                pub rax: usize,
                pub rem: usize,
                pub alp: usize,
                pub deg: u16,
            }

            impl TestSet {
                pub fn rax(&self) -> RawRow {
                    new_from_num!(self.rax).row
                }

                pub fn rem(&self) -> RawRow {
                    new_from_num!(self.rem).row
                }

                pub fn bdp(&self) -> RawRow {
                    let bdp = 10usize.pow(self.deg as u32);
                    new_from_num!(bdp).row
                }

                pub fn alp(&self) -> RawRow {
                    new_from_num!(self.alp).row
                }

                pub fn deg(&self) -> u16 {
                    self.deg
                }

                pub fn dgl(&self) -> u16 {
                    self.deg - 1
                }

                pub fn dbdlp(&self) -> RawRow {
                    let deg = self.deg;
                    let dbdlp = deg * 10u16.pow((deg - 1) as u32);
                    new_from_num!(dbdlp).row
                }
            }

            pub struct TestOuts {
                pub wrax: RawRow,
                pub rax_pow_less: RawRow,
                pub sub: RawRow,
                pub lim: RawRow,
                pub div: RawRow,
                pub beta: RawRow,
                pub betag: Option<bool>,
                pub incr: bool,
                pub decr: bool,
            }

            impl TestOuts {
                pub fn new() -> Self {
                    let empty = vec![];

                    TestOuts {
                        wrax: empty.clone(),
                        rax_pow_less: empty.clone(),
                        sub: empty.clone(),
                        lim: empty.clone(),
                        div: empty.clone(),
                        beta: empty.clone(),
                        betag: None,
                        incr: false,
                        decr: false,
                    }
                }
            }

            #[cfg(test)]
            mod tests_of_units {

                use super::{TestOuts, TestSet};

                #[test]
                fn test_set_test() {
                    let test = TestSet {
                        rax: 3,
                        rem: 15,
                        alp: 133,
                        deg: 3,
                    };

                    assert_eq!(vec![3], test.rax());
                    assert_eq!(vec![5, 1], test.rem());
                    assert_eq!(vec![0, 0, 0, 1], test.bdp());
                    assert_eq!(vec![3, 3, 1], test.alp());
                    assert_eq!(3, test.deg());
                    assert_eq!(2, test.dgl());
                    assert_eq!(vec![0, 0, 3], test.dbdlp());
                }

                #[test]
                fn test_outs_test() {
                    let outs = TestOuts::new();

                    assert_eq!(0, outs.wrax.len());
                    assert_eq!(0, outs.rax_pow_less.len());
                    assert_eq!(0, outs.sub.len());
                    assert_eq!(0, outs.lim.len());
                    assert_eq!(0, outs.div.len());
                    assert_eq!(0, outs.beta.len());
                    assert_eq!(None, outs.betag);
                    assert_eq!(false, outs.incr);
                    assert_eq!(false, outs.decr);
                }
            }
        }

        use super::super::next;
        use crate::{unity_raw, Row};
        use test_aides::{TestOuts, TestSet};

        #[test]
        fn basic_test() {
            let tset = TestSet {
                rax: 3,
                rem: 15,
                alp: 133,
                deg: 3,
            };

            let mut rax_ref = tset.rax();
            let unity = unity_raw();

            let mut outs = TestOuts::new();

            let rem_ref = next(
                &mut rax_ref,
                tset.rem(),
                &tset.bdp(),
                &tset.alp(),
                tset.deg(),
                tset.dgl(),
                &tset.dbdlp(),
                &unity,
                &mut outs,
            );

            let sub = 27_000;
            let lim = 15_133;
            let div = 2700;

            let beta = lim / div;
            let rem = lim - (34u32.pow(tset.deg() as u32) - sub);

            let sub = new_from_num!(sub).row;
            let lim = new_from_num!(lim).row;
            let div = new_from_num!(div).row;

            let beta = new_from_num!(beta).row;
            let rem = new_from_num!(rem).row;

            assert_eq!(vec![0, 3], outs.wrax);
            assert_eq!(vec![9], outs.rax_pow_less);
            assert_eq!(sub, outs.sub);
            assert_eq!(lim, outs.lim);
            assert_eq!(div, outs.div);

            assert_eq!(beta, outs.beta);
            assert_eq!(Some(true), outs.betag);

            assert_eq!(vec![4, 3], rax_ref);
            assert_eq!(rem, rem_ref);
        }

        #[test]
        fn rax_zero_test() {
            let tset = TestSet {
                rax: 0,
                rem: 0,
                alp: 133,
                deg: 3,
            };

            let unity = unity_raw();
            let mut outs = TestOuts::new();

            _ = next(
                &mut tset.rax(),
                tset.rem(),
                &tset.bdp(),
                &tset.alp(),
                tset.deg(),
                tset.dgl(),
                &tset.dbdlp(),
                &unity,
                &mut outs,
            );

            assert_eq!(vec![0], outs.wrax);
            assert_eq!(vec![0], outs.rax_pow_less);
            assert_eq!(vec![0], outs.sub);
            assert_eq!(vec![3, 3, 1], outs.lim);
            assert_eq!(Vec::<u8>::new(), outs.div);
            assert_eq!(vec![1], outs.beta);
            assert_eq!(Some(false), outs.betag);
        }

        #[test]
        fn degree_one_test() {
            let tset = TestSet {
                rax: 2,
                rem: 3,
                alp: 222,
                deg: 1,
            };

            let unity = unity_raw();

            let mut outs = TestOuts::new();

            _ = next(
                &mut tset.rax(),
                tset.rem(),
                &tset.bdp(),
                &tset.alp(),
                tset.deg(),
                tset.dgl(),
                &tset.dbdlp(),
                &unity,
                &mut outs,
            );

            assert_eq!(vec![0, 2], outs.wrax);
            assert_eq!(vec![1], outs.rax_pow_less);
            assert_eq!(vec![0, 2], outs.sub);
            assert_eq!(vec![2, 5, 2], outs.lim);
            assert_eq!(vec![1], outs.div);
            assert_eq!(vec![2, 5, 2], outs.beta);
            assert_eq!(Some(true), outs.betag);
        }

        #[test]
        fn g_zero_test() {
            let tset = TestSet {
                rax: 2,
                rem: 1,
                alp: 199,
                deg: 3,
            };

            let unity = unity_raw();

            let mut outs = TestOuts::new();

            _ = next(
                &mut tset.rax(),
                tset.rem(),
                &tset.bdp(),
                &tset.alp(),
                tset.deg(),
                tset.dgl(),
                &tset.dbdlp(),
                &unity,
                &mut outs,
            );

            assert_eq!(vec![0, 2], outs.wrax);
            assert_eq!(vec![4], outs.rax_pow_less);
            assert_eq!(vec![0, 0, 0, 8], outs.sub);
            assert_eq!(vec![9, 9, 1, 1], outs.lim);
            assert_eq!(vec![0, 0, 2, 1], outs.div);
            assert_eq!(vec![1], outs.beta);
            assert_eq!(Some(false), outs.betag);
        }

        #[test]
        fn g_one_test() {
            let tset = TestSet {
                rax: 2,
                rem: 2,
                alp: 399,
                deg: 3,
            };

            let unity = unity_raw();

            let mut outs = TestOuts::new();

            _ = next(
                &mut tset.rax(),
                tset.rem(),
                &tset.bdp(),
                &tset.alp(),
                tset.deg(),
                tset.dgl(),
                &tset.dbdlp(),
                &unity,
                &mut outs,
            );

            assert_eq!(vec![0, 2], outs.wrax);
            assert_eq!(vec![4], outs.rax_pow_less);
            assert_eq!(vec![0, 0, 0, 8], outs.sub);
            assert_eq!(vec![9, 9, 3, 2], outs.lim);
            assert_eq!(vec![0, 0, 2, 1], outs.div);
            assert_eq!(vec![1], outs.beta);
            assert_eq!(Some(false), outs.betag);
        }

        #[test]
        fn g_two_test() {
            let tset = TestSet {
                rax: 2,
                rem: 2,
                alp: 400,
                deg: 3,
            };

            let unity = unity_raw();

            let mut outs = TestOuts::new();

            _ = next(
                &mut tset.rax(),
                tset.rem(),
                &tset.bdp(),
                &tset.alp(),
                tset.deg(),
                tset.dgl(),
                &tset.dbdlp(),
                &unity,
                &mut outs,
            );

            assert_eq!(vec![0, 2], outs.wrax);
            assert_eq!(vec![4], outs.rax_pow_less);
            assert_eq!(vec![0, 0, 0, 8], outs.sub);
            assert_eq!(vec![0, 0, 4, 2], outs.lim);
            assert_eq!(vec![0, 0, 2, 1], outs.div);
            assert_eq!(vec![2], outs.beta);
            assert_eq!(Some(true), outs.betag);
        }

        #[test]
        fn incr_test() {
            // rax_pow_less =3² =9
            // dbdlp = 3 ⋅10² =300
            // div = dbdlp ⋅rax_pow_less =2700
            // lim = 10³ ⋅2 +791 =2791
            // g = ⌊lim ÷div⌋ =1

            // omax₁ =31³ =29791
            // omax₂ =31³ -10³ ⋅3³ =2791

            let tset = TestSet {
                rax: 3,
                rem: 2,
                alp: 791,
                deg: 3,
            };

            let unity = unity_raw();

            let mut outs = TestOuts::new();

            _ = next(
                &mut tset.rax(),
                tset.rem(),
                &tset.bdp(),
                &tset.alp(),
                tset.deg(),
                tset.dgl(),
                &tset.dbdlp(),
                &unity,
                &mut outs,
            );

            assert_eq!(vec![9], outs.rax_pow_less);
            assert_eq!(vec![1, 9, 7, 2], outs.lim);
            assert_eq!(vec![0, 0, 0, 7, 2], outs.sub);
            assert_eq!(vec![1], outs.beta);
            assert_eq!(vec![0, 0, 7, 2], outs.div);
            assert_eq!(Some(false), outs.betag);
            assert_eq!(true, outs.incr);
            assert_eq!(false, outs.decr);
        }

        #[test]
        fn decr_test() {
            // rax_pow_less =3² =9
            // dbdlp = 3 ⋅10² =300
            // div = dbdlp ⋅rax_pow_less =2700
            // lim = 10³ ⋅15 +874 =15874
            // g = ⌊lim ÷div⌋ =5

            // omax₁ =35³ =42875
            // omax₂ =35³ -10³ ⋅3³ =15875

            let tset = TestSet {
                rax: 3,
                rem: 15,
                alp: 874,
                deg: 3,
            };

            let unity = unity_raw();

            let mut outs = TestOuts::new();

            _ = next(
                &mut tset.rax(),
                tset.rem(),
                &tset.bdp(),
                &tset.alp(),
                tset.deg(),
                tset.dgl(),
                &tset.dbdlp(),
                &unity,
                &mut outs,
            );

            assert_eq!(vec![9], outs.rax_pow_less);
            assert_eq!(vec![4, 7, 8, 5, 1], outs.lim);
            assert_eq!(vec![0, 0, 0, 7, 2], outs.sub);
            assert_eq!(vec![5], outs.beta);
            assert_eq!(vec![0, 0, 7, 2], outs.div);
            assert_eq!(Some(true), outs.betag);
            assert_eq!(false, outs.incr);
            assert_eq!(true, outs.decr);
        }

        #[test]
        fn max_zero_test() {
            // rax_pow_less =2² =4
            // dbdlp = 3 ⋅10² =300
            // div = dbdlp ⋅rax_pow_less =1200
            // lim = 10³ ⋅1 +260 =1260
            // g = ⌊lim ÷div⌋ =1

            // omax₁ =21³ =9261
            // omax₂ =21³ -10³ ⋅2³ =1261

            let tset = TestSet {
                rax: 2,
                rem: 1,
                alp: 260,
                deg: 3,
            };

            let unity = unity_raw();
            let mut outs = TestOuts::new();

            _ = next(
                &mut tset.rax(),
                tset.rem(),
                &tset.bdp(),
                &tset.alp(),
                tset.deg(),
                tset.dgl(),
                &tset.dbdlp(),
                &unity,
                &mut outs,
            );

            assert_eq!(vec![4], outs.rax_pow_less);
            assert_eq!(vec![0, 6, 2, 1], outs.lim);
            assert_eq!(vec![0, 0, 0, 8], outs.sub);
            assert_eq!(vec![1], outs.beta);
            assert_eq!(vec![0, 0, 2, 1], outs.div);
            assert_eq!(Some(false), outs.betag);
            assert_eq!(false, outs.incr);
            assert_eq!(false, outs.decr);
        }
    }

    mod guess {
        use crate::Row;
        use crate::{nought_raw, nth_root::guess};

        #[test]
        fn rax_pow_less_zero_test() {
            let rax_pow_less = nought_raw();
            let empty = vec![];
            let mut div_out = vec![];
            let mut g_out = vec![];

            let g = guess(rax_pow_less, &empty, &empty, &mut div_out, &mut g_out);
            assert_eq!(None, g);
            assert_eq!(0, div_out.len());
            assert_eq!(0, g_out.len());
        }

        #[test]
        fn g_zero_test() {
            let rax_pow_less = new_from_num!(25).row;
            let dbdlp = new_from_num!(200).row;
            let lim = new_from_num!(4_999).row;
            let mut div_out = vec![];
            let mut g_out = vec![];

            let g = guess(rax_pow_less, &dbdlp, &lim, &mut div_out, &mut g_out);
            assert_eq!(None, g);
            assert_eq!(vec![0], g_out);
            assert_eq!(vec![0, 0, 0, 5], div_out);
        }

        #[test]
        fn g_one_test() {
            let rax_pow_less = new_from_num!(25).row;
            let dbdlp = new_from_num!(200).row;
            let lim = new_from_num!(5_000).row;
            let mut div_out = vec![];
            let mut g_out = vec![];

            let g = guess(rax_pow_less, &dbdlp, &lim, &mut div_out, &mut g_out);
            assert_eq!(None, g);
            assert_eq!(vec![1], g_out);
            assert_eq!(lim, div_out);
        }

        #[test]
        fn g_two_test() {
            let rax_pow_less = new_from_num!(25).row;
            let dbdlp = new_from_num!(200).row;
            let lim = new_from_num!(10_000).row;
            let mut div_out = vec![];
            let mut g_out = vec![];

            let g = guess(rax_pow_less, &dbdlp, &lim, &mut div_out, &mut g_out);
            assert_eq!(Some(vec![2]), g);
            assert_eq!(vec![0, 0, 0, 5], div_out);
        }
    }

    mod incr {
        use crate::nth_root::{incr, IncRes};
        use crate::{unity_raw, Row};

        struct Incr {
            wrax: usize,
            beta: usize,
            degree: u16,
            sub: usize,
            limit: usize,
            betag: bool,
        }

        impl Incr {
            pub fn incr(&self) -> IncRes {
                let wrax = new_from_num!(self.wrax).row;
                let beta = new_from_num!(self.beta).row;
                let sub = new_from_num!(self.sub).row;
                let lim = new_from_num!(self.limit).row;

                let betag = self.betag;
                let degree = self.degree;
                let unity = unity_raw();

                incr(&wrax, &beta, &unity, degree, &sub, &lim, betag)
            }
        }

        #[test]
        fn guess_too_much_test() {
            let test = Incr {
                wrax: 20,
                beta: 3,
                degree: 3,
                sub: 66,
                limit: 12_100,
                betag: true,
            };

            let res = test.incr();

            let orax = new_from_num!(23).row;
            assert_eq!(IncRes::OverGuess(orax), res);
        }

        #[test]
        // essentially, same as beta_is_beta_test
        fn guess_is_beta_test1() {
            let test = Incr {
                wrax: 20,
                beta: 3,
                degree: 3,
                sub: 67,
                limit: 12_100,
                betag: true,
            };

            let res = test.incr();

            let rax = new_from_num!(23).row;
            let max = new_from_num!(12100).row;

            assert_eq!(IncRes::Attainment((rax, max)), res);
        }

        #[test]
        fn guess_is_beta_test2() {
            let test = Incr {
                wrax: 20,
                beta: 3,
                degree: 3,
                sub: 68,
                limit: 12_100,
                betag: true,
            };

            let res = test.incr();

            let rax = new_from_num!(23).row;
            let max = new_from_num!(12099).row;

            assert_eq!(IncRes::Attainment((rax, max)), res);
        }

        #[test]
        fn beta_too_much_test() {
            let test = Incr {
                wrax: 20,
                beta: 1,
                degree: 3,
                sub: 60,
                limit: 9_200,
                betag: false,
            };

            let res = test.incr();

            assert_eq!(IncRes::MaxZero, res);
        }

        #[test]
        // essentially, same as guess_is_beta_test
        fn beta_is_beta_test1() {
            let test = Incr {
                wrax: 20,
                beta: 3,
                degree: 3,
                sub: 67,
                limit: 12_100,
                betag: false,
            };

            let res = test.incr();

            let rax = new_from_num!(23).row;
            let max = new_from_num!(12100).row;

            assert_eq!(IncRes::Attainment((rax, max)), res);
        }

        #[test]
        fn beta_is_beta_test2() {
            let test = Incr {
                wrax: 20,
                beta: 3,
                degree: 3,
                sub: 68,
                limit: 12_100,
                betag: false,
            };

            let res = test.incr();

            let rax = new_from_num!(23).row;
            let max = new_from_num!(12099).row;

            assert_eq!(IncRes::Attainment((rax, max)), res);
        }
    }

    mod decr {
        use crate::{unity_raw, RawRow, Row};

        use super::super::decr;

        struct Decr {
            orax: usize,
            deg: u16,
            sub: usize,
            lim: usize,
        }

        impl Decr {
            pub fn decr(&self) -> (RawRow, RawRow) {
                let mut orax = new_from_num!(self.orax).row;
                let sub = new_from_num!(self.sub).row;
                let lim = new_from_num!(self.lim).row;

                let unity = unity_raw();
                let degree = self.deg;

                let omax = decr(&mut orax, &unity, degree, &sub, &lim);
                (orax, omax)
            }
        }

        #[test]
        fn max_equal_lim_test() {
            let test = Decr {
                orax: 25,
                deg: 4,
                sub: 776,
                lim: 331_000,
            };

            let (orax, omax) = test.decr();

            let rax = new_from_num!(24).row;
            let max = new_from_num!(331_000).row;

            assert_eq!(rax, orax);
            assert_eq!(max, omax);
        }

        #[test]
        fn max_less_lim_test() {
            let test = Decr {
                orax: 25,
                deg: 4,
                sub: 777,
                lim: 331_000,
            };

            let (orax, omax) = test.decr();

            let rax = new_from_num!(24).row;
            let max = new_from_num!(330_999).row;

            assert_eq!(rax, orax);
            assert_eq!(max, omax);
        }

        #[test]
        fn subtracting_test() {
            let test = Decr {
                orax: 26,
                deg: 4,
                sub: 776,
                lim: 331_000,
            };

            let (orax, omax) = test.decr();

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

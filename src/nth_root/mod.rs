/// Variables and their meaning
/// --------------------------------------------------
/// B  — base (decadic)
/// n  — root/radix degree
/// x  — radicand
/// y  — root/radix
/// r  — remainder
/// α  — next n places of radicand
/// β  — root next increment
/// y' — new y for next iteration
/// r' — new r for next iteration
use std::cmp::max;

use crate::{
    addition_sum, addition_two, division, is_nought_raw, is_unity_raw, mul_raw, multiplication,
    nought_raw, pow_raw, rel_raw, subtraction_arithmetical, unity_raw, PlacesRow, RawRow, Rel, Row,
};

#[cfg(test)]
use tests_of_units::next::test_aides::NextTestOuts;

#[cfg(test)]
use tests_of_units::root::test_aides::RootTestOuts;

/// Computes `nth` integer root of `radicand`.
///
/// Returns `PlacesRow` with result or `None` for `0`ᵗʰ root.
pub fn root(
    radicand: &PlacesRow,
    nth: u16,
    #[cfg(test)] outs: &mut RootTestOuts,
    #[cfg(test)] no_shortcuts: bool,
) -> Option<PlacesRow> {
    if nth == 0 {
        return None;
    }

    let rad = &radicand.row;

    if let Some(res) = root_shortcut(
        rad,
        nth,
        #[cfg(test)]
        no_shortcuts,
    ) {
        return Some(res);
    }

    let base = &vec![0, 1];
    let unity = unity_raw();

    // n -1
    let nth_less = nth - 1;

    // Bⁿ⁻¹
    let bdpl = &pow_raw(base, nth_less, false);

    // decadic base powered by degree
    // base degree power
    // Bⁿ
    let bdp = multiplication(base, bdpl);

    // degree base degree less power
    // nBⁿ⁻¹
    let dbdlp = multiplication(&new_from_num_raw!(nth), bdpl);

    #[cfg(test)]
    {
        outs.bdp = bdp.clone();
        outs.nth_less = nth_less;
        outs.dbdlp = dbdlp.clone();
    }

    // root/radix
    // y
    let mut rax = nought_raw();
    // remainder
    // r
    let mut rem = nought_raw();

    let mut agen = AlphaGenerator::new(rad, nth as usize);

    loop {
        // α
        let alpha = agen.next();
        // operatives
        // y', r'
        let (orax, orem) = next(
            &rax,
            &rem,
            &bdp,
            &alpha,
            nth,
            nth_less,
            &dbdlp,
            &unity,
            #[cfg(test)]
            &mut NextTestOuts::new(),
        );

        let orax_pow = pow_raw(&orax, nth, false);

        let rel = rel_raw(&orax_pow, rad);
        if let Rel::Greater(_) = rel {
            #[cfg(test)]
            {
                outs.bcode = 1;
            }

            break;
        }

        rax = orax;

        if Rel::Equal == rel {
            #[cfg(test)]
            {
                outs.bcode = 2;
            }

            break;
        }

        rem = orem;
    }

    Some(Row { row: rax })
}

/// n >0, ⁿ√0 =0
/// n >0, ⁿ√1 =1
/// ¹√x =x
fn root_shortcut(rad: &RawRow, deg: u16, #[cfg(test)] skip: bool) -> Option<PlacesRow> {
    #[cfg(test)]
    if skip {
        return None;
    }

    return if deg == 1 || is_nought_raw(rad) || is_unity_raw(rad) {
        Some(PlacesRow { row: rad.clone() })
    } else {
        None
    };
}

fn next(
    rax: &RawRow,     // y
    rem: &RawRow,     // r
    bdp: &RawRow,     // Bⁿ
    alpha: &[u8],     // α
    degree: u16,      // n
    degree_less: u16, // n -1
    dbdlp: &RawRow,   // nBⁿ⁻¹
    unity: &RawRow,   // 1

    #[cfg(test)] outs: &mut NextTestOuts,
) -> (RawRow, RawRow) {
    // yⁿ⁻¹
    let rax_pow_less = pow_raw(&rax, degree_less, false);

    // Bⁿyⁿ, subtrahend
    let sub = mul_raw(bdp, multiplication(&rax_pow_less, &rax).as_slice(), false);

    let wrax_cap = rax.len() + 1;
    let mut wrax = Vec::new();
    wrax.reserve_exact(wrax_cap);
    wrax.push(0);

    // By, widen rax
    if is_nought_raw(&rax) == false {
        // y' =By +β, β =0

        unsafe {
            wrax.set_len(wrax_cap);
        };

        wrax[1..].copy_from_slice(&rax);
    }

    // Bⁿr +α, limit
    let mut lim = mul_raw(bdp, rem, false);
    addition_sum(alpha, &mut lim, 0);

    // let make initial guess, if possible
    let (betag, beta) = if let Some(g) = guess(
        &rax_pow_less,
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
        outs.wrax = wrax.clone();
        outs.rax_pow_less = rax_pow_less.clone();
        outs.sub = sub.clone();
        outs.lim = lim.clone();
        outs.beta = beta.clone();
        outs.betag = Some(betag);
    }

    let inc_res = incr(&wrax, &beta, unity, degree, &sub, &lim, betag);

    // (By +β)ⁿ -Bⁿyⁿ
    let (rax, max) = match inc_res {
        IncRes::Attainment((r, m)) => {
            #[cfg(test)]
            set_cr(&mut outs.incr);

            (r, m)
        }
        IncRes::MaxZero => {
            // (By +β)ⁿ -Bⁿyⁿ
            // β =0 =>(By)ⁿ -Bⁿyⁿ =0
            return (wrax, lim);
        }
        IncRes::OverGuess(mut or) => {
            #[cfg(test)]
            set_cr(&mut outs.decr);

            let m = decr(&mut or, unity, degree, &sub, &lim);

            (or, m)
        }
    };

    // r' =(Bⁿr +α) -((By +β)ⁿ -Bⁿyⁿ)
    _ = subtraction_arithmetical(&mut lim, &max);

    return (rax, lim);

    #[cfg(test)]
    fn set_cr(cr: &mut bool) {
        *cr = true;
    }
}

fn guess(
    rax_pow_less: &RawRow, // yⁿ⁻¹
    dbdlp: &RawRow,        // nBⁿ⁻¹
    lim: &RawRow,          // Bⁿr +α
    #[cfg(test)] div_out: &mut RawRow,
    #[cfg(test)] g_out: &mut RawRow,
) -> Option<RawRow> {
    if !is_nought_raw(rax_pow_less.as_slice()) {
        // nBⁿ⁻¹ ·yⁿ⁻¹
        let div = multiplication(dbdlp, rax_pow_less);

        #[cfg(test)]
        {
            *div_out = div.clone();
        }

        // (Bⁿr +α) ÷(nBⁿ⁻¹ ·yⁿ⁻¹)
        let g = division(
            lim,
            &div,
            #[cfg(test)]
            &mut vec![],
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
        let mut omax = pow_raw(&orax, degree, false);

        // (By +β)ⁿ -Bⁿyⁿ
        _ = subtraction_arithmetical(&mut omax, sub);

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

            _ = subtraction_arithmetical(&mut orax, unity);

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
        _ = subtraction_arithmetical(orax, unity);

        // (By +β)ⁿ
        let mut omax = pow_raw(&orax, degree, false);

        // (By +β)ⁿ -Bⁿyⁿ
        _ = subtraction_arithmetical(&mut omax, sub);

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

        let mut ix = self.ix;
        let alpha = &onum[ix..];
        self.onum = &onum[..ix];

        if ix > 0 {
            self.ix = ix - self.ras;
        }

        ix = alpha.len();

        while ix > 0 {
            ix -= 1;

            let num = alpha[ix];
            if num > 0 {
                break;
            }
        }

        &alpha[..=ix]
    }
}

#[cfg(test)]
mod tests_of_units {

    pub mod root {

        pub mod test_aides {
            use crate::RawRow;

            pub struct RootTestOuts {
                pub bcode: u32,
                pub bdp: RawRow,
                pub nth_less: u16,
                pub dbdlp: RawRow,
            }

            impl RootTestOuts {
                pub fn new() -> Self {
                    Self {
                        bcode: 0,
                        bdp: vec![],
                        nth_less: u16::MAX,
                        dbdlp: vec![],
                    }
                }
            }

            mod tests_of_units {
                use super::RootTestOuts;

                #[test]
                fn new_test() {
                    let outs = RootTestOuts::new();
                    assert_eq!(0, outs.bcode);
                    assert_eq!(0, outs.bdp.len());
                    assert_eq!(u16::MAX, outs.nth_less);
                    assert_eq!(0, outs.dbdlp.len());
                }
            }
        }

        use crate::{PlacesRow, Row};

        use super::super::root;
        use test_aides::RootTestOuts;

        #[test]
        fn basic_test() {
            let rad = new_from_num!(8);
            let proof = new_from_num!(2);
            let mut outs = RootTestOuts::new();

            assert_eq!(Some(proof), root(&rad, 3, &mut outs, false));
        }

        #[test]
        fn zero_root_test() {
            let rad = new_from_num!(u32::MAX);
            let mut outs = RootTestOuts::new();

            assert_eq!(None, root(&rad, 0, &mut outs, false));
        }

        #[test]
        fn first_root_test() {
            let vals = [0, 1, 2, 3, 10, 100, 999, 1_000_000, 9_999_999];
            let mut outs = RootTestOuts::new();

            for &v in vals.iter() {
                let rad = new_from_num!(v);
                assert_eq!(root(&rad, 1, &mut outs, true), Some(rad.clone()));
                assert_eq!(root(&rad, 1, &mut outs, false), Some(rad.clone()));
            }
        }

        #[test]
        fn root_of_zero_test() {
            let vals = [1, 2, 3, 4, 5, 100, 999];
            let mut outs = RootTestOuts::new();

            let nought = PlacesRow::nought();
            for &v in vals.iter() {
                assert_eq!(root(&nought, v, &mut outs, true), Some(nought.clone()));
                assert_eq!(root(&nought, v, &mut outs, false), Some(nought.clone()));
            }
        }

        #[test]
        fn root_of_one_test() {
            let vals = [1, 2, 3, 4, 5, 100, 999];
            let mut outs = RootTestOuts::new();

            let unity = PlacesRow::unity();
            for &v in vals.iter() {
                assert_eq!(root(&unity, v, &mut outs, true), Some(unity.clone()));
                assert_eq!(root(&unity, v, &mut outs, false), Some(unity.clone()));
            }
        }

        #[test]
        fn sqrt_basic_test() {
            #[rustfmt::skip]
            let vals = [
                (0, [0].as_slice()),
                (1, [1,3].as_slice()),
                (2, [4,8].as_slice()),
                (3, [9,15].as_slice()),
                (4, [16,24].as_slice()),
                (5, [25,35].as_slice()),
                (6, [36,48].as_slice()),];

            let mut outs = RootTestOuts::new();

            for v in vals.iter() {
                for &n in v.1 {
                    let proof = Some(new_from_num!(v.0));
                    let rad = new_from_num!(n);

                    assert_eq!(proof, root(&rad, 2, &mut outs, true));
                    assert_eq!(proof, root(&rad, 2, &mut outs, false));
                }
            }
        }

        #[test]
        fn cbrt_basic_test() {
            #[rustfmt::skip]
            let vals = [
                (0,[0].as_slice()),
                (1,[1,7].as_slice()), 
                (2,[8,26].as_slice()),
                (3,[27,63].as_slice()),
                (4,[64,124].as_slice()),
                (5,[125,215].as_slice())];

            let mut outs = RootTestOuts::new();

            for v in vals.iter() {
                for &n in v.1 {
                    let proof = Some(new_from_num!(v.0));
                    let rad = new_from_num!(n);

                    assert_eq!(proof, root(&rad, 3, &mut outs, true));
                    assert_eq!(proof, root(&rad, 3, &mut outs, false));
                }
            }
        }

        #[test]
        fn integer_root_test() {
            #[rustfmt::skip]
            let vals = [
                (4, 4, 256),
                (7, 5, 16_807),
                (100, 4, 1_00_00_00_00),
                (217, 3, 10_218_313),
                (5560, 2, 30_913_600),
                (1222, 3, 1_824_793_048), 
                (177, 4, 981_506_241),
                (793, 3, 498_677_257),
                (313, 3, 30_664_297),                    
                (4, 14, 268_435_456),            
                (2, 30, 1_073_741_824),                    
                (2, 31, 2147483648), 
                (4, 15, 1073741824),
            ];

            let mut outs = RootTestOuts::new();
            for v in vals {
                let proof = new_from_num!(v.0);
                let rad = PlacesRow::new_from_usize(v.2);

                assert_eq!(Some(proof), root(&rad, v.1, &mut outs, false));
            }
        }

        #[test]
        fn rounded_root_test() {
            #[rustfmt::skip]
            let vals = [
                (17, 2, 312),               // ≈ 17.7
                (9, 4, 9999),               // ≈ 9.9998
                (9, 3, 999),                // ≈ 9.997
                (9, 2, 99),                 // ≈ 9.95
                (99, 2, 9999),              // ≈ 99.995
                (21, 3, 9999),              // ≈ 21.5            
                (20, 4, 173_479),           // ≈ 20.41
                (2, 17, 16_777_215),        // ≈ 2.661            
                (3, 13, 33_554_431),        // ≈ 3.79            
                (31629, 2, 1_000_400_400),  // ≈ 31629.11
                (45, 5, 200_300_010),       // ≈ 45.7                                
                (5, 12, 900_900_009),       // ≈ 5.575
                (2, 26, 90_900_009),        // ≈ 2.02                                     
            ];

            let mut outs = RootTestOuts::new();

            for v in vals {
                let proof = new_from_num!(v.0);
                let rad = new_from_num!(v.2);

                assert_eq!(Some(proof), root(&rad, v.1, &mut outs, false));
            }
        }

        #[test]
        fn readme_test() {
            let mut outs = RootTestOuts::new();

            let test = PlacesRow::new_from_usize(99_999_999);
            let radicand = PlacesRow::new_from_str(
                "999999910000003599999916000001259999987400000083999999640000000899999999",
            )
            .unwrap();
            assert_eq!(Some(test), root(&radicand, 9, &mut outs, false));
        }

        #[test]
        fn expected_escape_test() {
            let mut outs = RootTestOuts::new();

            let rad = new_from_num!(256);
            _ = root(&rad, 4, &mut outs, false);
            assert_eq!(2, outs.bcode);

            let rad = new_from_num!(257);
            _ = root(&rad, 4, &mut outs, false);
            assert_eq!(1, outs.bcode);
        }

        #[test]
        fn degree_one_test() {
            let mut outs = RootTestOuts::new();
            let rad = new_from_num!(0);

            _ = root(&rad, 1, &mut outs, false);
            assert_eq!(0, outs.bdp.len());
            assert_eq!(u16::MAX, outs.nth_less);
            assert_eq!(0, outs.dbdlp.len());

            _ = root(&rad, 1, &mut outs, true);
            assert_eq!(vec![0, 1], outs.bdp);
            assert_eq!(0, outs.nth_less);
            assert_eq!(vec![1], outs.dbdlp);
        }

        #[test]
        fn computational_test() {
            let mut outs = RootTestOuts::new();
            let rad = new_from_num!(2);

            _ = root(&rad, 9, &mut outs, false);

            assert_eq!(new_from_num_raw!(1_000_000_000), outs.bdp);
            assert_eq!(8, outs.nth_less);
            assert_eq!(new_from_num_raw!(900_000_000), outs.dbdlp);
        }

        #[test]
        #[cfg(feature = "ext-tests")]
        fn load_test() {
            let vals = [
                ("99999999999999999999999999999999999999", 9, "16681"),
                (
                    "1111111111111111111111111111111111111111",
                    1,
                    "1111111111111111111111111111111111111111",
                ),
                (
                    "25252525252525252525252525252525252525252525252525252525",
                    25,
                    "164",
                ),
                (
                    "7777777777777777777777777777777777777117777777777777777777777777777777777777",
                    11,
                    "7928092",
                ),
            ];

            let mut outs = RootTestOuts::new();

            for v in vals {
                let proof = Row::new_from_str(v.2).unwrap();
                let rad = Row::new_from_str(v.0).unwrap();

                assert_eq!(Some(proof), root(&rad, v.1, &mut outs, false));
            }
        }
    }

    mod root_shortcut {
        use crate::{nought_raw, unity_raw, PlacesRow, Row};

        use super::super::root_shortcut;

        #[test]
        fn nought_root_test() {
            let nought = nought_raw();
            let proof = PlacesRow::nought();

            assert_eq!(root_shortcut(&nought, u16::MAX, false), Some(proof));
        }

        #[test]
        fn unity_root_test() {
            let unity = unity_raw();
            let proof = PlacesRow::unity();

            assert_eq!(root_shortcut(&unity, u16::MAX, false), Some(proof));
        }

        #[test]
        fn deg_1_test() {
            let rad = new_from_num!(u128::MAX);
            assert_eq!(root_shortcut(&rad.row, 1, false), Some(rad));
        }

        #[test]
        fn none_of_cases_test() {
            let rad = new_from_num_raw!(2);
            assert_eq!(root_shortcut(&rad, 2, false), None);
        }

        #[test]
        fn skip_test() {
            let unity = nought_raw();
            assert_eq!(root_shortcut(&unity, 1, true), None);
        }
    }

    pub mod next {

        pub mod test_aides {
            use crate::RawRow;

            pub struct NextTestSet {
                pub rax: usize,
                pub rem: usize,
                pub alp: usize,
                pub deg: u16,
            }

            impl NextTestSet {
                pub fn rax(&self) -> RawRow {
                    new_from_num_raw!(self.rax)
                }

                pub fn rem(&self) -> RawRow {
                    new_from_num_raw!(self.rem)
                }

                pub fn bdp(&self) -> RawRow {
                    let bdp = 10usize.pow(self.deg as u32);
                    new_from_num_raw!(bdp)
                }

                pub fn alp(&self) -> RawRow {
                    new_from_num_raw!(self.alp)
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
                    new_from_num_raw!(dbdlp)
                }
            }

            pub struct NextTestOuts {
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

            impl NextTestOuts {
                pub fn new() -> Self {
                    let empty = vec![];

                    NextTestOuts {
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

                use super::{NextTestOuts, NextTestSet};

                #[test]
                fn test_set_test() {
                    let test = NextTestSet {
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
                    let outs = NextTestOuts::new();

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
        use crate::unity_raw;
        use test_aides::{NextTestOuts, NextTestSet};

        #[test]
        fn basic_test() {
            let tset = NextTestSet {
                rax: 3,
                rem: 15,
                alp: 133,
                deg: 3,
            };

            let unity = unity_raw();

            let mut outs = NextTestOuts::new();

            let (rax, rem) = next(
                &tset.rax(),
                &tset.rem(),
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
            let rem_proof = lim - (34u32.pow(tset.deg() as u32) - sub);

            let sub = new_from_num_raw!(sub);
            let lim = new_from_num_raw!(lim);
            let div = new_from_num_raw!(div);

            let beta = new_from_num_raw!(beta);
            let rem_proof = new_from_num_raw!(rem_proof);

            assert_eq!(vec![0, 3], outs.wrax);
            assert_eq!(vec![9], outs.rax_pow_less);
            assert_eq!(sub, outs.sub);
            assert_eq!(lim, outs.lim);
            assert_eq!(div, outs.div);

            assert_eq!(beta, outs.beta);
            assert_eq!(Some(true), outs.betag);

            assert_eq!(vec![4, 3], rax);
            assert_eq!(rem_proof, rem);
        }

        #[test]
        fn rax_zero_test() {
            let tset = NextTestSet {
                rax: 0,
                rem: 0,
                alp: 133,
                deg: 3,
            };

            let unity = unity_raw();
            let mut outs = NextTestOuts::new();

            _ = next(
                &mut tset.rax(),
                &tset.rem(),
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
            let tset = NextTestSet {
                rax: 2,
                rem: 3,
                alp: 222,
                deg: 1,
            };

            let unity = unity_raw();

            let mut outs = NextTestOuts::new();

            _ = next(
                &mut tset.rax(),
                &tset.rem(),
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
            let tset = NextTestSet {
                rax: 2,
                rem: 1,
                alp: 199,
                deg: 3,
            };

            let unity = unity_raw();

            let mut outs = NextTestOuts::new();

            _ = next(
                &mut tset.rax(),
                &tset.rem(),
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
            let tset = NextTestSet {
                rax: 2,
                rem: 2,
                alp: 399,
                deg: 3,
            };

            let unity = unity_raw();

            let mut outs = NextTestOuts::new();

            _ = next(
                &mut tset.rax(),
                &tset.rem(),
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
            let tset = NextTestSet {
                rax: 2,
                rem: 2,
                alp: 400,
                deg: 3,
            };

            let unity = unity_raw();

            let mut outs = NextTestOuts::new();

            _ = next(
                &mut tset.rax(),
                &tset.rem(),
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

            let tset = NextTestSet {
                rax: 3,
                rem: 2,
                alp: 791,
                deg: 3,
            };

            let unity = unity_raw();

            let mut outs = NextTestOuts::new();

            _ = next(
                &mut tset.rax(),
                &tset.rem(),
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

            let tset = NextTestSet {
                rax: 3,
                rem: 15,
                alp: 874,
                deg: 3,
            };

            let unity = unity_raw();

            let mut outs = NextTestOuts::new();

            _ = next(
                &mut tset.rax(),
                &tset.rem(),
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

            let tset = NextTestSet {
                rax: 2,
                rem: 1,
                alp: 260,
                deg: 3,
            };

            let unity = unity_raw();
            let mut outs = NextTestOuts::new();

            _ = next(
                &mut tset.rax(),
                &tset.rem(),
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

        use crate::{nought_raw, nth_root::guess};

        #[test]
        fn rax_pow_less_zero_test() {
            let rax_pow_less = nought_raw();
            let empty = vec![];
            let mut div_out = vec![];
            let mut g_out = vec![];

            let g = guess(&rax_pow_less, &empty, &empty, &mut div_out, &mut g_out);
            assert_eq!(None, g);
            assert_eq!(0, div_out.len());
            assert_eq!(0, g_out.len());
        }

        #[test]
        fn g_zero_test() {
            let rax_pow_less = new_from_num_raw!(25);
            let dbdlp = new_from_num_raw!(200);
            let lim = new_from_num_raw!(4_999);
            let mut div_out = vec![];
            let mut g_out = vec![];

            let g = guess(&rax_pow_less, &dbdlp, &lim, &mut div_out, &mut g_out);
            assert_eq!(None, g);
            assert_eq!(vec![0], g_out);
            assert_eq!(vec![0, 0, 0, 5], div_out);
        }

        #[test]
        fn g_one_test() {
            let rax_pow_less = new_from_num_raw!(25);
            let dbdlp = new_from_num_raw!(200);
            let lim = new_from_num_raw!(5_000);
            let mut div_out = vec![];
            let mut g_out = vec![];

            let g = guess(&rax_pow_less, &dbdlp, &lim, &mut div_out, &mut g_out);
            assert_eq!(None, g);
            assert_eq!(vec![1], g_out);
            assert_eq!(lim, div_out);
        }

        #[test]
        fn g_two_test() {
            let rax_pow_less = new_from_num_raw!(25);
            let dbdlp = new_from_num_raw!(200);
            let lim = new_from_num_raw!(10_000);
            let mut div_out = vec![];
            let mut g_out = vec![];

            let g = guess(&rax_pow_less, &dbdlp, &lim, &mut div_out, &mut g_out);
            assert_eq!(Some(vec![2]), g);
            assert_eq!(vec![0, 0, 0, 5], div_out);
        }

        #[test]
        fn g_ten_test() {
            let rax_pow_less = new_from_num_raw!(25);
            let dbdlp = new_from_num_raw!(200);
            let lim = new_from_num_raw!(50_000);
            let mut div_out = vec![];
            let mut g_out = vec![];

            let g = guess(&rax_pow_less, &dbdlp, &lim, &mut div_out, &mut g_out);
            assert_eq!(Some(vec![0, 1]), g);
            assert_eq!(vec![0, 0, 0, 5], div_out);
        }
    }

    mod incr {
        use crate::nth_root::{incr, IncRes};
        use crate::unity_raw;

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
                let wrax = new_from_num_raw!(self.wrax);
                let beta = new_from_num_raw!(self.beta);
                let sub = new_from_num_raw!(self.sub);
                let lim = new_from_num_raw!(self.limit);

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

            let orax = new_from_num_raw!(23);

            match res {
                IncRes::OverGuess(r) => {
                    assert_eq!(orax, r);
                    assert_eq!(3, r.capacity());
                }
                _ => assert!(false),
            }
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

            let rax = new_from_num_raw!(23);
            let max = new_from_num_raw!(12100);

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

            let rax = new_from_num_raw!(23);
            let max = new_from_num_raw!(12099);

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

            let rax = new_from_num_raw!(23);
            let max = new_from_num_raw!(12100);

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

            let rax = new_from_num_raw!(23);
            let max = new_from_num_raw!(12099);

            assert_eq!(IncRes::Attainment((rax, max)), res);
        }
    }

    mod decr {
        use crate::{unity_raw, RawRow};

        use super::super::decr;

        struct Decr {
            orax: usize,
            deg: u16,
            sub: usize,
            lim: usize,
        }

        impl Decr {
            pub fn decr(&self) -> (RawRow, RawRow) {
                let mut orax = new_from_num_raw!(self.orax);
                let sub = new_from_num_raw!(self.sub);
                let lim = new_from_num_raw!(self.lim);

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

            let rax = new_from_num_raw!(24);
            let max = new_from_num_raw!(331_000);

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

            let rax = new_from_num_raw!(24);
            let max = new_from_num_raw!(330_999);

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

            let rax = new_from_num_raw!(24);
            let max = new_from_num_raw!(331_000);

            assert_eq!(rax, orax);
            assert_eq!(max, omax);
        }
    }

    mod alpha_generator {
        use super::super::AlphaGenerator;

        use crate::nought_raw;

        #[test]
        fn lesser_root_test() {
            let vals = [
                (1_234_567, 3, [1, 234, 567, 0, 0]),
                (11_2222_3333, 4, [11, 2222, 3333, 0, 0]),
            ];

            for v in vals {
                let num = new_from_num_raw!(v.0);
                let mut generator = AlphaGenerator::new(&num, v.1);

                for p in v.2 {
                    let proof = new_from_num_raw!(p);

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
                let num = new_from_num_raw!(v.0);
                let mut generator = AlphaGenerator::new(&num, v.1);

                for p in v.2 {
                    let proof = new_from_num_raw!(p);

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
                let num = new_from_num_raw!(v.0);
                let mut generator = AlphaGenerator::new(&num, v.1);

                for p in v.2 {
                    let proof = new_from_num_raw!(p);

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
        fn zero_place_omission_test() {
            let vals = [
                (1_000_000, 3, [1, 0, 0]),
                (1_100_100, 3, [1, 100, 100]),
                (1_010_010, 3, [1, 10, 10]),
                (1_001_001, 3, [1, 1, 1]),
            ];

            for v in vals {
                let num = new_from_num_raw!(v.0);
                let mut generator = AlphaGenerator::new(&num, v.1);

                for p in v.2 {
                    let proof = new_from_num_raw!(p);

                    let next = generator.next();
                    assert_eq!(proof, next);
                }
            }
        }

        #[test]
        #[should_panic(expected = "0ᵗʰ root is strictly unsupported computation.")]
        fn zero_root_test() {
            let number = new_from_num_raw!(u32::MAX);
            let root = 0;

            _ = AlphaGenerator::new(&number, root);
        }
    }
}

// cargo fmt & cargo test --release nth_root
// cargo fmt & cargo test --release --features ext-tests nth_root

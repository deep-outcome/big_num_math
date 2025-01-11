//! Allows to compute on big numbers. No negative numbers support. Provides only some
//! basic mathematical functions.

#![no_std]

extern crate alloc;
type RawRow = Vec<u8>;
type Row = PlacesRow;

/// `PlacesRow` represents row of decimal places starting at ones (`0` index).
#[derive(Clone, PartialEq, Debug)]
pub struct PlacesRow {
    row: RawRow,
}

use core::{cmp::Ordering, ops::Deref};
impl Deref for PlacesRow {
    type Target = [u8];

    /// View into internal storage.
    fn deref(&self) -> &[u8] {
        self.row.as_slice()
    }
}

impl PlacesRow {
    /// Strong ctor for usage with prebuilded raw places row.
    ///
    /// Only ones are allowed in `row`.
    /// Places in `row` have to be ordered from ones over tens, hundreds, … to highest place;
    /// from 0-index to last-index.
    ///
    /// Leading zeros are truncated. Does not change capacity.
    ///
    /// Returns `PlacesRow` or index where place > `9` was
    /// encountered. `None` for 0-len `row`.
    pub fn new_from_vec(mut row: Vec<u8>) -> Result<Self, Option<usize>> {
        if row.len() == 0 {
            return Err(None);
        }

        let row_len = len_without_leading_raw(&row, 0, 1);

        for ix in 0..row_len {
            if row[ix] > 9 {
                return Err(Some(ix));
            }
        }

        row.truncate(row_len);
        Ok(Row { row })
    }

    /// Handy ctor for usage with _classic_ primitive numeric data type.
    pub fn new_from_num(mut num: u128) -> Self {
        let mut row = Vec::new();
        loop {
            let d = num % 10;
            row.push(d as u8);
            num = num / 10;

            if num == 0 {
                break;
            }
        }

        Row { row }
    }

    /// Handy ctor for usage with long numbers.
    ///
    /// Only digits are allowed in `s`. Leading zeros are ommitted.
    ///
    /// Returns `PlacesRow` or index in `s` where uncovertable `char` was
    /// encountered. `None` for empty string.
    pub fn new_from_str(mut s: &str) -> Result<Self, Option<usize>> {
        let s_len_orig = s.len();
        if s_len_orig == 0 {
            return Err(None);
        }

        s = s.trim_start_matches('0');
        let s_len = s.len();

        let row = if s_len == 0 {
            nought_raw()
        } else {
            let mut row = Vec::new();
            row.reserve_exact(s_len);

            let mut err_inx = s_len_orig;
            for (c, sc) in s.chars().rev().zip(row.spare_capacity_mut()) {
                err_inx -= 1;
                if c.is_ascii_digit() {
                    let n = from_digit(c);
                    sc.write(n);
                } else {
                    return Err(Some(err_inx));
                }
            }

            unsafe { row.set_len(s_len) }
            row
        };

        Ok(Row { row })
    }

    /// Returns `String` representation.
    pub fn to_number(&self) -> String {
        let row = &self.row;
        let len = row.len();
        let mut number = String::new();
        number.reserve_exact(len);
        for i in row.iter().rev() {
            let digit = to_digit(*i);
            number.push(digit);
        }

        number
    }

    /// `true` if and only if `PlacesRow` is _unity_ value.
    pub fn is_unity(&self) -> bool {
        is_unity_raw(&self.row)
    }

    /// `true` if and only if `PlacesRow` is _nought_ value.
    pub fn is_nought(&self) -> bool {
        is_nought_raw(&self.row)
    }

    /// Returns unity `PlacesRow`.
    pub fn unity() -> PlacesRow {
        Row { row: unity_raw() }
    }

    /// Returns nought `PlacesRow`.
    pub fn nought() -> PlacesRow {
        Row { row: nought_raw() }
    }

    #[deprecated(since = "2.2.0", note = "Pick `fn nought` instead.")]
    /// Returns zero `PlacesRow`.
    pub fn zero() -> PlacesRow {
        Self::nought()
    }

    /// Returns decimal places count.
    ///
    /// Check with `DecCnt` for detail on count properties.
    pub fn places(&self) -> usize {
        dec_pla_cnt_raw(&self.row)
    }
}

fn shrink_to_fit_raw(row: &mut RawRow) {
    truncate_leading_raw(row, 0, 1);
    row.shrink_to_fit();
}

fn truncate_leading_raw(row: &mut RawRow, lead: u8, upto: usize) {
    let new_len = len_without_leading_raw(row, lead, upto);
    row.truncate(new_len);
}

fn len_without_leading_raw(row: &RawRow, lead: u8, upto: usize) -> usize {
    let mut row_len = row.len();
    for ix in (upto..row_len).rev() {
        if lead == row[ix] {
            row_len -= 1;
        } else {
            break;
        }
    }

    row_len
}

fn unity_raw() -> RawRow {
    vec![1; 1]
}

fn nought_raw() -> RawRow {
    vec![0; 1]
}

fn is_unity_raw(row: &RawRow) -> bool {
    is_one_raw(row, 1)
}

fn is_nought_raw(row: &RawRow) -> bool {
    is_one_raw(row, 0)
}

fn is_one_raw(row: &RawRow, one: u8) -> bool {
    row.len() == 1 && row[0] == one
}

fn from_digit(c: char) -> u8 {
    match c {
        '0' => 0,
        '1' => 1,
        '2' => 2,
        '3' => 3,
        '4' => 4,
        '5' => 5,
        '6' => 6,
        '7' => 7,
        '8' => 8,
        '9' => 9,
        _ => panic!("Unsupported char `{c}` conversion."),
    }
}

fn to_digit(n: u8) -> char {
    match n {
        0 => '0',
        1 => '1',
        2 => '2',
        3 => '3',
        4 => '4',
        5 => '5',
        6 => '6',
        7 => '7',
        8 => '8',
        9 => '9',
        _ => panic!("Only number < 10 supported."),
    }
}

impl alloc::string::ToString for PlacesRow {
    /// Returns `String` representation.
    fn to_string(&self) -> String {
        self.to_number()
    }
}

use core::convert::From;
impl From<u128> for PlacesRow {
    /// Converts `value` into `PlacesRow`.
    fn from(value: u128) -> Self {
        Self::new_from_num(value)
    }
}

/// Represents 1,000 numbers of √10 ≈ 3.16.
///
/// Check with `fn ord_of_mag`.
pub const SQUARE_ROOT_TEN_COMPARATOR: &str = "3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148548856030453880014690519596700153903344921657179259940659150153474113339484124085316929577090471576461044369257879062037808609941828371711548406328552999118596824564203326961604691314336128949791890266529543612676178781350061388186278580463683134952478031143769334671973819513185678403231241795402218308045872844614600253577579702828644029024407977896034543989163349222652612067792651676031048436697793756926155720500369894909469421850007358348844643882731109289109042348054235653403907274019786543725939641726001306990000955784463109626790694418336130181302894541703315807731626386395193793704654765220632063686587197822049312426053454111609356979828132452297000798883523759585328579251362964686511497675217123459559238039375625125369855194955325099947038843990336466165470647234999796132343403021857052187836676345789510732982875157945215771652139626324438399018484560935762602";

/// Order of magnitude computational kind.
#[derive(Clone, PartialEq, Debug)]
pub enum OomKind {
    /// Uses `√10` for relation.    
    ///
    /// Check with `SQUARE_ROOT_TEN_COMPARATOR`.
    Strict,
    /// Uses `5` for relation.
    Loose,
}

/// Order of magnitude enumeration.
#[derive(Clone, PartialEq, Debug)]
pub enum Oom {
    /// Order of magnitude is not defined for nought `PlacesRow`.
    Undefined,
    /// Precise _oom_.
    ///
    /// Check with `Approx(usize)` variant.
    Precise(usize),
    /// Approximated _oom_ is result of operation on `PlacesRow` requiring
    /// greater precision than provided by `SQUARE_ROOT_TEN_COMPARATOR`.
    ///
    /// Check with `fn ord_of_mag`.
    Approx(usize),
}

/// Computes order of magnitude for `num` and `kind`.
///
/// OOM is defined for number _n_ as follows:
///
/// n = u ⋅ 10ⁱ, v ÷10 ≤ u < v, v = √10 ∨ v = 5
///
/// Then _i_ is order of magnitude of such number.
///
/// `Strict` kind evaluation is precise up to 1,000 numbers of `SQUARE_ROOT_TEN_COMPARATOR`.
/// Any `num` requiring higher precision is considered to be of higher order. That
/// means its order of magnitude is arranged equal to its decimal places count
/// and is reported as `Oom::Approx(usize)`.
///
/// Returns `Oom` enumeration.
pub fn ord_of_mag(num: &PlacesRow, kind: OomKind) -> Oom {
    let row = &num.row;
    if is_nought_raw(row) {
        return Oom::Undefined;
    }

    let cmp = match kind {
        OomKind::Strict => SQUARE_ROOT_TEN_COMPARATOR.chars().map(from_digit).collect(),
        OomKind::Loose => vec![5],
    };

    let row_len = row.len();
    let cmp_len = cmp.len();

    let mut row_ix = row_len;
    let mut cmp_ix = 0;

    let mut num_less = None;

    loop {
        if row_ix == 0 || cmp_ix == cmp_len {
            break;
        }

        row_ix = row_ix - 1;

        if row[row_ix] < cmp[cmp_ix] {
            num_less = Some(true);
            break;
        }

        if row[row_ix] > cmp[cmp_ix] {
            num_less = Some(false);
            break;
        }

        cmp_ix = cmp_ix + 1;
    }

    let (num_less, precise) = if let Some(l) = num_less {
        (l, true)
    } else {
        let ord = row_len.cmp(&cmp_len);
        match ord {
            Ordering::Greater => (false, kind == OomKind::Loose),
            Ordering::Less => (true, true),
            _ => (false, true),
        }
    };

    let oom = if num_less { row_len - 1 } else { row_len };

    match precise {
        true => Oom::Precise(oom),
        false => Oom::Approx(oom),
    }
}

/// Relation enumeration.
///
/// ```
/// use big_num_math::{rel, PlacesRow, Rel, DecCnt};
/// let num_1 = PlacesRow::new_from_num(100);
/// let num_2 = PlacesRow::new_from_num(101);
/// let num_3 = PlacesRow::new_from_num(1);
///
/// assert_eq!(Rel::Lesser(None), rel(&num_1, &num_2));
/// let cnt_1_cnt_2_dif: DecCnt = (1,3,2);
/// assert_eq!(Rel::Lesser(Some(cnt_1_cnt_2_dif)), rel(&num_3, &num_1));
/// ```
#[derive(Debug, PartialEq, Clone)]
pub enum Rel {
    /// Greater than comparand. Holds information about decimal difference, if there is some.
    Greater(Option<DecCnt>),
    /// Equal to comparand.
    Equal,
    /// Lesser than comparand. Holds information about decimal difference, if there is some.
    Lesser(Option<DecCnt>),
}

/// Checks relation of `num` to `comparand`.
///
/// Returns `Rel` relation.
pub fn rel(num: &PlacesRow, comparand: &PlacesRow) -> Rel {
    let r1 = &num.row;
    let r2 = &comparand.row;

    rel_raw(r1, r2)
}

fn rel_raw(r1: &RawRow, r2: &RawRow) -> Rel {
    match rel_dec_raw(r1, r2) {
        RelDec::Greater(c) => Rel::Greater(Some(c)),
        RelDec::Lesser(c) => Rel::Lesser(Some(c)),
        RelDec::Equal(c) => {
            let mut rel = Rel::Equal;
            for inx in (0..c).rev() {
                if r1[inx] > r2[inx] {
                    rel = Rel::Greater(None);
                    break;
                } else if r1[inx] < r2[inx] {
                    rel = Rel::Lesser(None);
                    break;
                }
            }

            rel
        }
    }
}

/// Decimal places count.
///
/// Tuple fields describe places count and are defined as follow.
/// |Name|Meaning    |
/// |:--:|:--------- |
/// |0   |number     |
/// |1   |comparand  |
/// |2   |difference |
///
/// Count relates to power of ten as table evinces.
/// |  Count |    Relation                  |
/// |:------:|:------------:                |
/// | 0      | number < 10⁰ ⇒ number = 0    |
/// | 1      | number < 10¹ ∧ number ≥ 10⁰  |
/// | 2      | number < 10² ∧ number ≥ 10¹  |
/// | ⋮      |   ⋮                          |
/// | n      | number < 10ⁿ ∧ number ≥ 10ⁿ⁻¹|
pub type DecCnt = (usize, usize, usize);

/// Decimal relation enumeration.
///
/// Expresses relation of numbers in decimal places count.
///
/// ```
/// use big_num_math::{rel_dec, PlacesRow, RelDec, DecCnt};
/// let num_1 = PlacesRow::new_from_num(333);
/// let num_2 = PlacesRow::new_from_num(777);
/// let num_3 = PlacesRow::new_from_num(1);
///
/// assert_eq!(RelDec::Equal(3), rel_dec(&num_1, &num_2));
/// let cnt_1_cnt_2_dif: DecCnt = (1,3,2);
/// assert_eq!(RelDec::Lesser(cnt_1_cnt_2_dif), rel_dec(&num_3, &num_1));
/// ```
#[derive(Debug, PartialEq, Clone)]
pub enum RelDec {
    /// Count greater than comparand has. Holds information about respective counts.
    Greater(DecCnt),
    /// Count equal to comparand count. Holds count information.
    Equal(usize),
    /// Count lesser than comparand has. Holds information about respective counts.
    Lesser(DecCnt),
}

/// Compares decimal places count of `num` and `comparand`.
///
/// Beware of nought values comparison. `fn deref` allows to view internal
/// storage and for nought it has some length, exactly 1, but count would be `0` exactly.
///
/// Returns `RelDec` relation.
pub fn rel_dec(num: &PlacesRow, comparand: &PlacesRow) -> RelDec {
    let r1 = &num.row;
    let r2 = &comparand.row;

    rel_dec_raw(r1, r2)
}

// ⟺ no leading zeros
// num.len() > comparand.len() ⇒ num > comparand
// num.len() < comparand.len() ⇒ num < comparand
// num.len() = comparand.len() ⇒ num ⪒ comparand
fn rel_dec_raw(r1: &RawRow, r2: &RawRow) -> RelDec {
    let r1_cnt = dec_pla_cnt_raw(r1);
    let r2_cnt = dec_pla_cnt_raw(r2);

    if r1_cnt == r2_cnt {
        return RelDec::Equal(r1_cnt);
    }

    let mut cnts = (r1_cnt, r2_cnt, 0);

    return if r1_cnt > r2_cnt {
        cnts.2 = r1_cnt - r2_cnt;
        RelDec::Greater(cnts)
    } else {
        cnts.2 = r2_cnt - r1_cnt;
        RelDec::Lesser(cnts)
    };
}

fn dec_pla_cnt_raw(r: &RawRow) -> usize {
    if is_nought_raw(r) {
        0
    } else {
        r.len()
    }
}

use alloc::{string::String, vec, vec::Vec};

/// Computes `addend1` and `addend2` sum.
///
/// Returns `PlacesRow` with result.
pub fn add(addend1: &PlacesRow, addend2: &PlacesRow) -> PlacesRow {
    let r1 = &addend1.row;
    let r2 = &addend2.row;

    match add_shortcut(r1, r2) {
        Some(row) => return Row { row },
        _ => {}
    }

    let (addend, augend) = if r1.len() > r2.len() {
        (r1, r2)
    } else {
        (r2, r1)
    };

    // avoids repetetive reallocations
    // +1 stands for contigent new place
    let mut sum = Vec::new();
    sum.reserve_exact(addend.len() + 1);

    #[cfg(test)]
    let sum_ptr = sum.as_ptr();

    addition(addend, Some(augend), &mut sum, 0);

    #[cfg(test)]
    assert!(sum_ptr == sum.as_ptr());

    Row { row: sum }
}

// 0 +x = x
// x +0 = x
fn add_shortcut(addend1: &RawRow, addend2: &RawRow) -> Option<RawRow> {
    if is_nought_raw(addend1) {
        Some(addend2.clone())
    } else if is_nought_raw(addend2) {
        Some(addend1.clone())
    } else {
        None
    }
}

/// Computes `minuend` and `subtrahend` difference.
///
/// Returns difference `PlacesRow` if `minuend` ≥ `subtrahend`, `None` otherwise.
pub fn sub(minuend: &PlacesRow, subtrahend: &PlacesRow) -> Option<PlacesRow> {
    let minuend = &minuend.row;
    let subtrahend = &subtrahend.row;

    match sub_shortcut(minuend, subtrahend) {
        Some(res) => return res,
        None => {}
    };

    let diff = subtraction(
        &minuend,
        &subtrahend,
        false,
        #[cfg(test)]
        &mut 0,
    )
    .0;
    Some(Row { row: diff })
}

// x -0 = x
// x -x = 0
// a -b, a < b not supported
fn sub_shortcut(minuend: &RawRow, subtrahend: &RawRow) -> Option<Option<Row>> {
    if is_nought_raw(subtrahend) {
        let row = Row {
            row: minuend.clone(),
        };
        return Some(Some(row));
    }

    return match rel_raw(minuend, subtrahend) {
        Rel::Lesser(_) => Some(None),
        Rel::Equal => Some(Some(Row::nought())),
        _ => return None,
    };
}

/// Computes `factor1` and `factor2` product.
///
/// Returns `PlacesRow` with result.
pub fn mul(factor1: &PlacesRow, factor2: &PlacesRow) -> PlacesRow {
    let factor1 = &factor1.row;
    let factor2 = &factor2.row;

    match mul_shortcut(factor1, factor2) {
        Some(row) => return Row { row },
        None => {}
    };

    mulmul(factor1, factor2, 1)
}

// x ⋅0 = 0
// 0 ⋅x = 0
//
// 1 ⋅x = x
// x ⋅1 = x
fn mul_shortcut(factor1: &RawRow, factor2: &RawRow) -> Option<RawRow> {
    if is_nought_raw(factor1) || is_nought_raw(factor2) {
        Some(nought_raw())
    } else if is_unity_raw(factor1) {
        Some(factor2.clone())
    } else if is_unity_raw(factor2) {
        Some(factor1.clone())
    } else {
        None
    }
}

/// Computes power `pow` of `base`.
///
/// Potentially CPU, memory intesive.
///
/// Returns `PlacesRow` with result.
pub fn pow(base: &PlacesRow, pow: u16) -> PlacesRow {
    let row = &base.row;

    if let Some(row) = pow_shortcut(row, pow) {
        return row;
    }

    mulmul(row, row, pow - 1)
}

// x⁰ = 1
// x¹ = x
// 0ⁿ = 0 n∊ℕ﹥₀
// 1ⁿ = 1 n∊ℕ₀
fn pow_shortcut(row: &RawRow, pow: u16) -> Option<Row> {
    if pow == 0 {
        Some(Row::unity())
    } else if pow == 1 {
        Some(Row { row: row.clone() })
    } else if is_nought_raw(row) {
        Some(Row::nought())
    } else if is_unity_raw(row) {
        Some(Row::unity())
    } else {
        None
    }
}

/// Computes `dividend` and `divisor` ratio and remainder.
///
/// Returns tuple with `PlacesRow` ratio and `PlacesRow` remainder in order or `None` when `divisor` is nought.
pub fn divrem(dividend: &PlacesRow, divisor: &PlacesRow) -> Option<(PlacesRow, PlacesRow)> {
    let dividend = &dividend.row;
    let divisor = &divisor.row;

    match divrem_shortcut(dividend, divisor) {
        Some(res) => return res,
        None => {}
    }

    let remratio = divrem_acceleration(
        &dividend,
        &divisor,
        #[cfg(test)]
        &mut 0,
        #[cfg(test)]
        &mut 0,
    );

    Some((Row { row: remratio.1 }, Row { row: remratio.0 }))
}

// x ∶0, illegal
// x ∶1 = x
// a ∶b = 0Ra, a << b, a ≪ b
fn divrem_shortcut(dividend: &RawRow, divisor: &RawRow) -> Option<Option<(Row, Row)>> {
    if is_nought_raw(divisor) {
        return Some(None);
    }

    let end_clone = || Row {
        row: dividend.clone(),
    };

    let shortcut = if is_unity_raw(divisor) {
        (end_clone(), Row::nought())
    } else {
        match rel_dec_raw(dividend, divisor) {
            RelDec::Lesser(_) => (Row::nought(), end_clone()),
            _ => return None,
        }
    };

    Some(Some(shortcut))
}

// in order to avoid highly excessive looping, divrem computation can be speed up
// by simple substracting divisor 10 products first
fn divrem_acceleration(
    dividend: &RawRow,
    divisor: &RawRow,
    #[cfg(test)] w_ctr: &mut usize,
    #[cfg(test)] ctr: &mut usize,
) -> (RawRow, RawRow) {
    let divisor_len = divisor.len();
    let mut remend_len = dividend.len();

    let mut ratio = vec![0];

    if remend_len < divisor_len {
        return (dividend.clone(), ratio);
    }

    let mut remainder = None;
    let mut end = dividend;

    if remend_len > divisor_len {
        // widen divisor
        let mut wdsor = vec![0; remend_len];
        // e.g. 15 000 ÷ 15
        // 5 -2 +1 = 4
        // mpler = [0,0,0,1], one at 4ᵗʰ place
        let mut mpler = vec![0; remend_len - divisor_len + 1];

        // highest index
        let sor_hg_ix = divisor_len - 1;

        // can run in vain when remend_len == divisor_len +1 and
        // divisor cannot be broaden up, also incurs extra reentrancy
        // at function end
        //   🡺 opt: shorcut execution
        loop {
            #[cfg(test)]
            {
                *w_ctr += 1;
            }

            let mut wr_ix = remend_len - 1;

            let mut l_ix = wr_ix;
            let mut r_ix = sor_hg_ix;

            loop {
                let end_num = end[l_ix];
                let sor_num = divisor[r_ix];

                // check whether divisor can be broaded up to
                // end highest place
                if end_num < sor_num {
                    wr_ix -= 1;
                    break;
                }

                if end_num > sor_num {
                    break;
                }

                if r_ix == 0 {
                    break;
                }

                l_ix -= 1;
                r_ix -= 1;
            }

            #[cfg(test)]
            {
                // sor is always widen upto highest or second highestmost place
                assert!(remend_len == wr_ix + 1 || remend_len == wr_ix + 2)
            }

            let wdsor_len = wr_ix + 1;

            // shortening wdsor removes leading numbers
            // which could influence computation in arithmetic
            // (significants) or execution (zeros) means
            unsafe { wdsor.set_len(wdsor_len) };

            let mut sor_ix = sor_hg_ix;
            loop {
                wdsor[wr_ix] = divisor[sor_ix];

                if sor_ix == 0 {
                    break;
                }

                sor_ix -= 1;
                wr_ix -= 1;
            }

            let remrat = subtraction(
                end,
                &wdsor,
                true,
                #[cfg(test)]
                ctr,
            );

            // e.g. 15 000 ÷ 25 ⇒ 2 500
            // 4 -2 = 2 ⇒ [0,0,1], one at index 2
            //
            // if mpler_wr_ix = 0 then multiplication is redundant
            //   🡺 opt: shorcut execution
            let mpler_wr_ix = wdsor_len - divisor_len;

            // previous "extensions" are stripped simply
            // by length shrinking
            unsafe { mpler.set_len(mpler_wr_ix + 1) };
            mpler[mpler_wr_ix] = 1;

            //   🡺 opt: let mulmul return only RawRow
            let rat = mulmul(&remrat.1, &mpler, 1);
            addition(&rat.row, None, &mut ratio, 0);

            remainder = Some(remrat.0);

            end = remainder.as_ref().unwrap();
            remend_len = end.len();

            if remend_len < divisor_len {
                return (remainder.unwrap(), ratio);
            } else if remend_len == divisor_len {
                // if end is nought and divisor_len = 1
                // this break is redundant
                //   🡺 opt: shorcut execution
                break;
            }
        }
    }

    // runs only when remend_len == divisor_len
    // if end is already rem this "runs in vain"

    let (rem, rat) = subtraction(
        end,
        &divisor,
        true,
        #[cfg(test)]
        ctr,
    );

    let rat = if remainder.is_some() {
        addition(&rat, None, &mut ratio, 0);
        ratio
    } else {
        rat
    };

    (rem, rat)
}

/// Combined method allows to compute multiplication and power using shared code.
///
/// Space for effecient power computation?
///   🡺 Inspect log₂ power speed up.
fn mulmul(row1: &RawRow, row2: &RawRow, times: u16) -> Row {
    let (mpler, mut mcand) = (row1, row2.clone());

    #[cfg(feature = "one-power-mulmul-support")]
    if times == 0 {
        return Row { row: mcand };
    }

    let mpler_len = mpler.len();

    // intermediate product of `mcand` and `mpler`
    let mut i_product = Vec::with_capacity(0);
    // intermediate sum of intermediate products
    let mut i_sum = Vec::with_capacity(0);

    let mut cntr = 0;
    loop {
        let mcand_len = mcand.len();

        // avoids repetetive reallocations
        // +1 stands for contigent new place
        i_product.reserve(mcand_len + 1);
        // avoids repetetive reallocations
        // places count of product cannot
        // be greater than sum of places of operands
        i_sum.reserve(mcand_len + mpler_len);

        #[cfg(test)]
        let i_product_ptr = i_product.as_ptr();

        #[cfg(test)]
        let i_sum_ptr = i_sum.as_ptr();

        for offset in 0..mpler_len {
            product(mpler[offset], &mcand, &mut i_product);
            addition(&i_product, None, &mut i_sum, offset);
            i_product.clear();
        }

        #[cfg(test)]
        assert!(i_product_ptr == i_product.as_ptr());

        #[cfg(test)]
        assert!(i_sum_ptr == i_sum.as_ptr());

        cntr += 1;
        if cntr == times {
            mcand = i_sum;
            break;
        }

        mcand.clear();
        let swap = mcand;
        mcand = i_sum;
        i_sum = swap;
    }

    // useless when both of factors cannot be nought
    shrink_to_fit_raw(&mut mcand);
    Row { row: mcand }
}

/// Computes product of `mpler` and `mcand`.
fn product(mpler: u8, mcand: &RawRow, product: &mut RawRow) {
    let mut takeover = 0;

    // runs in vain for `mpler` = 0
    //   🡺 inspect possibilities
    for &num in mcand {
        // each `prod` can be immediately added to intermediate sum
        //   🡺 inspect this option
        let prod = mpler * num;
        let prod = ones(prod, &mut takeover);
        product.push(prod);
    }

    if takeover != 0 {
        product.push(takeover);
    }
}

/// Adds `addend_1` to `sum` or adds `addend_1` and `addend_2` sum into `sum`.
///
/// Precise expectations must be upkept when adding 2 addends: sum is assumed to be empty, `addend_1` to be longer or equal of numbers and offset to be `0`.
fn addition(addend_1: &RawRow, addend_2: Option<&RawRow>, sum: &mut RawRow, offset: usize) {
    let addend_1_len = addend_1.len();

    let (addend_2_ptr, addend_2_len) = if let Some(addend) = addend_2 {
        (addend.as_ptr(), addend.len())
    } else {
        (sum.as_ptr(), sum.len())
    };

    let mut takeover = 0;
    let mut addend_1_inx = 0;
    let mut addend_2_inx = offset;

    loop {
        let addend_1_available = addend_1_inx < addend_1_len;
        if !addend_1_available && takeover == 0 {
            break;
        }

        let addend_1_num = if addend_1_available {
            addend_1[addend_1_inx]
        } else {
            0
        };

        let addend_2_num = if addend_2_inx < addend_2_len {
            unsafe { addend_2_ptr.offset(addend_2_inx as isize).read() }
        } else {
            0
        };

        let add = ones(addend_2_num + addend_1_num, &mut takeover);
        if let Some(refer) = sum.get_mut(addend_2_inx) {
            *refer = add;
        } else {
            sum.push(add);
        }

        addend_1_inx += 1;
        addend_2_inx += 1;
    }
}

/// For difference computation applies precondition minuend ≥ subtrahend.
/// Returns difference/remainder and ration in order.
//
// NOTE: Support for longer subtrahend implies extended guard condition on
// correction `inx < subtrahend_len && inx < minuend_len`. See feature 'shorter-dividend-support'.
fn subtraction(
    minuend: &RawRow,
    subtrahend: &RawRow,
    remainder: bool,
    #[cfg(test)] ctr: &mut usize,
) -> (RawRow, RawRow) {
    let mut diffrem_populated = false;

    let minuend_len = minuend.len();
    let subtrahend_len = subtrahend.len();

    let mut diffrem = vec![0; minuend_len];
    let diffrem_ptr = diffrem.as_ptr();
    let mut minuend_ptr = minuend.as_ptr();

    let mut ratio = nought_raw();
    let one = vec![1; 1];
    let mut takeover;
    let mut inx;
    loop {
        #[cfg(test)]
        {
            *ctr += 1;
        }

        takeover = 0;
        inx = 0;

        while inx < minuend_len {
            let s_num = if inx < subtrahend_len {
                subtrahend[inx]
            } else if takeover == 0 && diffrem_populated {
                break;
            } else {
                0
            };

            let mut m_num = unsafe { minuend_ptr.offset(inx as isize).read() };

            let total_s = s_num + takeover;
            takeover = if m_num < total_s {
                m_num += 10;
                1
            } else {
                0
            };

            diffrem[inx] = m_num - total_s;
            inx += 1;
        }

        // existing remainder implies _minuend_ exhaustion
        // thus remainder is one turn more than is correct
        if takeover == 1 {
            inx = 0;
            takeover = 0;
            while inx < subtrahend_len {
                let correction = diffrem[inx] + subtrahend[inx];
                diffrem[inx] = ones(correction, &mut takeover);
                inx += 1;
            }

            truncate_leading_raw(&mut diffrem, 9, inx);
            break;
        }

        addition(&one, None, &mut ratio, 0);

        if !remainder {
            break;
        }

        if !diffrem_populated {
            minuend_ptr = diffrem_ptr;
            diffrem_populated = true;
        }
    }

    shrink_to_fit_raw(&mut diffrem);
    (diffrem, ratio)
}

/// Supports algorithimical decimal row computations.
/// Solve problem as ones to ones addition.
/// Takes current size of place `num`, adds takeover
/// `takeover_ref` to it, returns ones of summation
/// and sets up `takeover_ref` with tens of summation.
fn ones(num: u8, takeover_ref: &mut u8) -> u8 {
    let mut takeover_val = *takeover_ref;
    let total = num + takeover_val;

    takeover_val = total / 10;
    *takeover_ref = takeover_val;

    total - takeover_val * 10
}

#[cfg(test)]
mod tests_of_units {

    use crate::RawRow;

    fn unity() -> RawRow {
        [1].to_vec()
    }

    fn nought() -> RawRow {
        [0].to_vec()
    }

    mod placesrow {
        use crate::Row;
        use alloc::string::ToString;

        mod new_from_vec {
            use crate::Row;
            use alloc::vec;

            #[test]
            fn basic_test() {
                let row = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
                let proof = row.clone();
                let row = Row::new_from_vec(row);

                assert!(row.is_ok());
                assert_eq!(proof, row.unwrap().row);
            }

            #[test]
            fn zero_len_test() {
                let row = Row::new_from_vec(vec![0; 0]);
                assert!(row.is_err());
                assert_eq!(None, row.err().unwrap());
            }

            #[test]
            fn unsupported_num_len_index_test() {
                let row = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 0];
                let row = Row::new_from_vec(row);

                assert!(row.is_err());
                assert_eq!(Some(10), row.err().unwrap());
            }

            #[test]
            fn unsupported_num_0_index_test() {
                let row = vec![10, 0, 0, 0];
                let row = Row::new_from_vec(row);

                assert!(row.is_err());
                assert_eq!(Some(0), row.err().unwrap());
            }

            #[test]
            fn leading_zeros_trim_test() {
                let row = Row::new_from_vec(vec![1, 2, 0, 0]);
                assert_eq!(&[1, 2], &*row.unwrap().row);
            }

            #[test]
            fn zero_reduction_test() {
                let row = Row::new_from_vec(vec![0, 0, 0, 0]);
                assert_eq!(&[0], &*row.unwrap().row);
            }
        }

        #[test]
        fn new_from_num_test() {
            let row = Row::new_from_num(000_1234567890);
            assert_eq!(&[0, 9, 8, 7, 6, 5, 4, 3, 2, 1], &*row);
        }

        mod new_from_str {
            use crate::Row;

            #[test]
            fn zero_len_test() {
                let row = Row::new_from_str("");
                assert!(row.is_err());
                assert_eq!(None, row.err().unwrap());
            }

            #[test]
            fn leading_zeros_trim_test() {
                let row = Row::new_from_str("0021");
                assert!(row.is_ok());
                assert_eq!(&[1, 2], &*row.unwrap().row);
            }

            #[test]
            fn zeros_reduction_test() {
                let row = Row::new_from_str("0000");
                assert!(row.is_ok());
                assert_eq!(&[0], &*row.unwrap().row);
            }

            #[test]
            fn nondigit_str_test() {
                let row = Row::new_from_str("0012w123");
                assert!(row.is_err());
                let inx = row.err().unwrap();
                assert!(inx.is_some());
                assert_eq!(4, inx.unwrap());
            }

            #[test]
            fn basic_test() {
                let row = Row::new_from_str("1234567890");
                assert!(row.is_ok());
                assert_eq!(&[0, 9, 8, 7, 6, 5, 4, 3, 2, 1], &*row.unwrap().row);
            }
        }

        mod to_number {
            use crate::Row;
            use alloc::vec;

            #[test]
            fn basic_test() {
                let row = Row::new_from_vec(vec![0, 9, 8, 7, 6, 5, 4, 3, 2, 1]).unwrap();
                assert_eq!("1234567890", row.to_number().as_str());
            }
        }

        use super::{nought, unity};
        #[test]
        fn is_unity_test() {
            let test = Row { row: unity() };
            assert_eq!(true, test.is_unity());
        }

        #[test]
        fn is_nought_test() {
            let test = Row { row: nought() };
            assert_eq!(true, test.is_nought());
        }

        #[test]
        fn unity_test() {
            let proof = Row { row: unity() };
            assert_eq!(proof, Row::unity());
        }

        #[test]
        fn nought_test() {
            let proof = Row { row: nought() };
            assert_eq!(proof, Row::nought());
        }

        #[test]
        #[allow(deprecated)]
        fn zero_test() {
            assert_eq!(&[0], &*Row::zero());
        }

        #[test]
        fn places_test() {
            let unity = Row::unity();
            assert_eq!(1, unity.places());
        }

        #[test]
        fn to_string_test() {
            let row = Row::new_from_num(1);
            assert_eq!("1", row.to_string());
        }

        #[test]
        fn from_test() {
            let row: Row = From::from(123);
            assert_eq!(&[3, 2, 1], &*row);
        }
    }

    mod shrink_to_fit_raw {
        use crate::shrink_to_fit_raw;
        use alloc::vec::Vec;

        #[test]
        fn zero_truncation_test() {
            let cap = 100;
            let mut row = Vec::with_capacity(cap);
            row.push(1);
            row.push(2);
            row.push(0);

            shrink_to_fit_raw(&mut row);
            assert_eq!(&[1, 2], &*row);
            assert!(row.capacity() < cap);
        }

        #[test]
        fn first_preservation_test() {
            let cap = 100;
            let mut row = Vec::with_capacity(cap);
            row.push(0);
            row.push(0);
            row.push(0);

            shrink_to_fit_raw(&mut row);
            assert_eq!(&[0], &*row);
            assert!(row.capacity() < cap);
        }
    }

    mod truncate_leading_raw {
        use crate::truncate_leading_raw;
        use alloc::vec;

        #[test]
        fn basic_test() {
            let mut row = vec![7, 7, 7, 7, 7];
            truncate_leading_raw(&mut row, 7, 3);
            assert_eq!(vec![7, 7, 7,], row);
        }
    }

    mod len_without_leading_raw {
        use crate::len_without_leading_raw;
        use alloc::vec;

        #[test]
        fn counting_test() {
            let count = len_without_leading_raw(&vec![1, 2, 5, 5, 5], 5, 0);
            assert_eq!(2, count);
        }

        #[test]
        fn preservation_test() {
            let count = len_without_leading_raw(&vec![5, 5, 5, 5], 5, 1);
            assert_eq!(1, count);
        }

        #[test]
        fn no_leading_test() {
            let count = len_without_leading_raw(&vec![5, 5, 5, 0], 5, 0);
            assert_eq!(4, count);
        }

        #[test]
        fn upto_equal_len_test() {
            let count = len_without_leading_raw(&vec![5, 5, 5], 5, 3);
            assert_eq!(3, count);
        }
    }

    use crate::{is_nought_raw, is_unity_raw, nought_raw, unity_raw};
    #[test]
    fn unity_raw_test() {
        assert_eq!(unity(), unity_raw());
    }

    #[test]
    fn nought_raw_test() {
        assert_eq!(nought(), nought_raw());
    }

    #[test]
    fn is_unity_raw_test() {
        assert_eq!(true, is_unity_raw(&unity()));
    }

    #[test]
    fn is_nought_raw_test() {
        assert_eq!(true, is_nought_raw(&nought()));
    }

    mod is_one_raw_test {
        use crate::is_one_raw;

        #[test]
        fn is() {
            let test = [3].to_vec();
            assert_eq!(true, is_one_raw(&test, 3));
        }

        #[test]
        fn different() {
            let test = [3].to_vec();
            assert_eq!(false, is_one_raw(&test, 4));
        }

        #[test]
        fn longer() {
            let test = [3, 3].to_vec();
            assert_eq!(false, is_one_raw(&test, 3));
        }
    }

    mod from_digit {
        extern crate std;

        use crate::from_digit;
        use alloc::format;
        use alloc::string::{String, ToString};
        use std::panic::catch_unwind;

        #[test]
        fn basic_test() {
            for proof in 0..=9 {
                let test = from_digit(proof.to_string().chars().next().unwrap());
                assert_eq!(proof, test);
            }
        }

        #[test]
        fn unsupported_char_test() {
            let uc = ['0' as u8 - 1, '9' as u8 + 1];

            for c in uc {
                let c = c as char;

                let proof = format!("Unsupported char `{c}` conversion.");
                let catch = catch_unwind(|| from_digit(c));

                assert!(catch.is_err());
                let err = catch.unwrap_err().downcast::<String>().unwrap();
                assert_eq!(proof, *err);
            }
        }
    }

    mod to_digit {
        use crate::to_digit;
        use alloc::string::ToString;

        #[test]
        fn basic_test() {
            for n in 0..=9 {
                let test = to_digit(n);
                let proof = n.to_string().chars().next().unwrap();
                assert_eq!(proof, test);
            }
        }

        #[test]
        #[should_panic(expected = "Only number < 10 supported.")]
        fn less_than_10_support_only_test() {
            to_digit(10);
        }
    }

    mod ord_of_mag {

        use crate::{ord_of_mag, Oom, OomKind, PlacesRow, Row};

        const PROOF: &str = "3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148548856030453880014690519596700153903344921657179259940659150153474113339484124085316929577090471576461044369257879062037808609941828371711548406328552999118596824564203326961604691314336128949791890266529543612676178781350061388186278580463683134952478031143769334671973819513185678403231241795402218308045872844614600253577579702828644029024407977896034543989163349222652612067792651676031048436697793756926155720500369894909469421850007358348844643882731109289109042348054235653403907274019786543725939641726001306990000955784463109626790694418336130181302894541703315807731626386395193793704654765220632063686587197822049312426053454111609356979828132452297000798883523759585328579251362964686511497675217123459559238039375625125369855194955325099947038843990336466165470647234999796132343403021857052187836676345789510732982875157945215771652139626324438399018484560935762602";

        #[test]
        fn consts_test() {
            use crate::SQUARE_ROOT_TEN_COMPARATOR;

            assert_eq!(1000, SQUARE_ROOT_TEN_COMPARATOR.len());
            assert_eq!(PROOF, SQUARE_ROOT_TEN_COMPARATOR);
        }

        #[test]
        fn nought_test() {
            let r = Row::nought();
            let oom = unsafe { core::mem::transmute::<u8, OomKind>(u8::MAX) };

            assert_eq!(Oom::Undefined, ord_of_mag(&r, oom));
        }

        #[test]
        fn readme_sample_test() {
            let number_1 = PlacesRow::new_from_num(3162277660168379331998893544432);
            let number_2 = PlacesRow::new_from_num(3162277660168379331998893544433);

            assert_eq!(Oom::Precise(30), ord_of_mag(&number_1, OomKind::Strict));
            assert_eq!(Oom::Precise(31), ord_of_mag(&number_2, OomKind::Strict));
            assert_eq!(Oom::Precise(30), ord_of_mag(&number_2, OomKind::Loose));
        }

        mod strict {
            use alloc::string::String;

            use super::PROOF;
            use crate::{ord_of_mag, Oom, OomKind::Strict, Row};

            #[test]
            fn universal_test() {
                #[rustfmt::skip]
                // lesser-shorter-greater triplets
                let values = [
                    (2,0), (3, 0), (4, 1),
                    (30, 1), (31, 1), (32, 2),                    
                    (315, 2), (316, 2), (317, 3), 
                    (3161, 3), (3162, 3), (3163, 4),                       
                    (316_227_765, 8), (316_227_766, 8), (316_227_767, 9),                                   
                ];

                for v in values {
                    let r = Row::new_from_num(v.0);
                    let o = ord_of_mag(&r, Strict);

                    assert_eq!(Oom::Precise(v.1), o, "{:?}", v);
                }
            }

            #[test]
            fn full_precision_test() {
                let r = Row::new_from_str(PROOF).unwrap();
                let o = ord_of_mag(&r, Strict);

                assert_eq!(Oom::Precise(PROOF.len()), o);
            }

            #[test]
            fn behind_precision_test() {
                let mut proof = String::from(PROOF);
                proof.push('0');

                let r = Row::new_from_str(proof.as_str()).unwrap();
                let o = ord_of_mag(&r, Strict);

                let proof_len = proof.len();
                assert_eq!(1001, proof_len);
                assert_eq!(Oom::Approx(proof_len), o);
            }
        }

        mod loose {
            use crate::{ord_of_mag, Oom, OomKind::Loose, Row};

            #[test]
            fn universal_test() {
                #[rustfmt::skip]
                let values = [                    
                    // lesser-equal-greater triplet
                    (4, 0)    , (5, 1)     , (6, 1),                    
                    // lesser-longer-greater triplets
                    (40, 1)   , (50, 2)    , (60, 2),                                                                                                                        
                    (4000, 3) , (5000, 4)  , (6000, 4)                                                                                                                                                                
                ];

                for v in values {
                    let r = Row::new_from_num(v.0);
                    let o = ord_of_mag(&r, Loose);

                    assert_eq!(Oom::Precise(v.1), o, "{:?}", v);
                }
            }
        }
    }

    // Relational comparison.
    mod rel {
        use crate::{rel, Rel, Row};

        #[test]
        fn basic_test() {
            let num = Row::new_from_num(155);
            assert_eq!(Rel::Equal, rel(&num, &num));
        }
    }

    mod rel_raw {

        use crate::{rel_raw, Rel, Row};

        #[test]
        fn longer_test() {
            let num = Row::new_from_num(11).row;
            let comparand = Row::new_from_num(9).row;

            let proof = Rel::Greater(Some((2, 1, 1)));
            assert_eq!(proof, rel_raw(&num, &comparand));
        }

        #[test]
        fn shorter_test() {
            let num = Row::new_from_num(9).row;
            let comparand = Row::new_from_num(10).row;

            let proof = Rel::Lesser(Some((1, 2, 1)));
            assert_eq!(proof, rel_raw(&num, &comparand));
        }

        #[test]
        fn greater_test() {
            let num_num = 1234567899;
            let cpd_num = 1234567890;

            let num = Row::new_from_num(num_num).row;
            let comparand = Row::new_from_num(cpd_num).row;

            assert_eq!(Rel::Greater(None), rel_raw(&num, &comparand));
        }

        #[test]
        fn equal_test() {
            let num = Row::new_from_num(1234567890);
            assert_eq!(Rel::Equal, rel_raw(&num.row, &num.row));
        }

        #[test]
        fn lesser_test() {
            let num_num = 1234567890;
            let cpd_num = 1234567899;

            let num = Row::new_from_num(num_num).row;
            let comparand = Row::new_from_num(cpd_num).row;

            assert_eq!(Rel::Lesser(None), rel_raw(&num, &comparand));
        }

        #[test]
        fn both_nought_test() {
            let num = Row::new_from_num(0).row;

            assert_eq!(Rel::Equal, rel_raw(&num, &num));
        }
    }

    mod rel_dec {
        use crate::{rel_dec, RelDec, Row};

        #[test]
        fn basic_test() {
            let num = Row::new_from_num(9876543210);

            assert_eq!(RelDec::Equal(10), rel_dec(&num, &num));
        }

        #[test]
        #[rustfmt::skip]
        fn readme_sample_test() {
            let number    = Row::new_from_str("1489754132134687989463132131").unwrap();
            let comparand = Row::new_from_str(        "48645698946456531371").unwrap();
            let decrel = rel_dec(&number, &comparand);

            assert_eq!(RelDec::Greater((28, 20, 8)), decrel);
        }
    }

    mod rel_dec_raw {
        use crate::{rel_dec_raw, RelDec, Row};

        #[test]
        fn equal_test() {
            let num = Row::new_from_num(9876543210).row;

            assert_eq!(RelDec::Equal(10), rel_dec_raw(&num, &num));
        }

        #[test]
        fn lesser_test() {
            let num = Row::new_from_num(10).row;
            let comparand = Row::new_from_num(9876543210).row;

            let proof = RelDec::Lesser((2, 10, 8));
            assert_eq!(proof, rel_dec_raw(&num, &comparand));
        }

        #[test]
        fn greater_test() {
            let num = Row::new_from_num(9876543210).row;
            let comparand = Row::new_from_num(10).row;

            let proof = RelDec::Greater((10, 2, 8));
            assert_eq!(proof, rel_dec_raw(&num, &comparand));
        }

        #[test]
        fn nought_test() {
            let num = Row::new_from_num(0).row;

            assert_eq!(RelDec::Equal(0), rel_dec_raw(&num, &num));
        }
    }

    mod dec_pla_cnt_raw {
        use alloc::vec;

        use crate::dec_pla_cnt_raw;

        #[test]
        fn nought_test() {
            let nought = vec![0; 1];
            assert_eq!(0, dec_pla_cnt_raw(&nought));
        }

        #[test]
        fn basic_test() {
            for test in [vec![1; 1], vec![1; 100]] {
                assert_eq!(test.len(), dec_pla_cnt_raw(&test));
            }
        }

        #[test]
        // function falsely reports zero len as nought
        // zero len happens nowhere, yet noted
        fn zero_len_pseudo_test() {
            let zero_len = vec![9; 0];
            assert_eq!(0, dec_pla_cnt_raw(&zero_len));
        }
    }

    // Addition.
    mod add {
        use crate::{add, Row};

        #[test]
        fn basic_test() {
            let row1 = Row::new_from_num(4);
            let row2 = Row::new_from_num(5);

            let sum = add(&row1, &row2);
            assert_eq!(&[9], &*sum.row);
        }

        #[test]
        fn left_num_longer_test() {
            let row1 = Row::new_from_num(10_000);
            let row2 = Row::new_from_num(5);

            let sum = add(&row1, &row2);
            assert_eq!(Row::new_from_num(10_005), sum);
        }

        #[test]
        fn right_num_longer_test2() {
            let row1 = Row::new_from_num(5);
            let row2 = Row::new_from_num(10_000);

            let sum = add(&row1, &row2);
            assert_eq!(Row::new_from_num(10_005), sum);
        }

        #[test]
        fn advanced_test() {
            let row = Row::new_from_str("680564733841876926926749214863536422910").unwrap();

            let sum = add(&row, &row);
            assert_eq!("1361129467683753853853498429727072845820", sum.to_number());
        }

        #[test]
        fn addend1_nought_test() {
            let addend1 = Row::nought();
            let addend2 = Row::new_from_num(4321);
            let sum = add(&addend1, &addend2);
            assert_eq!(addend2, sum);
        }

        #[test]
        fn addend2_nought_test() {
            let addend1 = Row::new_from_num(4321);
            let addend2 = Row::nought();
            let sum = add(&addend1, &addend2);
            assert_eq!(addend1, sum);
        }
    }

    mod add_shortcut {
        use crate::{add_shortcut, nought_raw, unity_raw};

        #[test]
        fn none_nought_test() {
            assert_eq!(None, add_shortcut(&unity_raw(), &unity_raw()));
        }

        use alloc::vec;
        #[test]
        fn r1_nought_test() {
            let r1 = nought_raw();
            let r2 = vec![1, 2, 3, 4];
            let res = add_shortcut(&r1, &r2);
            assert_eq!(Some(r2.clone()), res);
            assert_ne!(r2.as_ptr(), res.unwrap().as_ptr());
        }

        #[test]
        fn r2_nought_test() {
            let r1 = vec![1, 2, 3, 4];
            let r2 = nought_raw();
            let res = add_shortcut(&r1, &r2);
            assert_eq!(Some(r1.clone()), res);
            assert_ne!(r1.as_ptr(), res.unwrap().as_ptr());
        }
    }

    /// Subtraction.
    mod sub {
        use crate::{sub, Row};

        #[test]
        fn lesser_minuend_test() {
            let minuend = Row::new_from_num(4);
            let subtrahend = Row::new_from_num(5);

            assert!(sub(&minuend, &subtrahend).is_none());
        }

        #[test]
        fn universal_test() {
            for triplet in [(99, 11, 88), (133, 133, 0), (90, 19, 71), (700, 699, 1)] {
                let minuend = Row::new_from_num(triplet.0);
                let subtrahend = Row::new_from_num(triplet.1);

                let proof = Row::new_from_num(triplet.2);
                let diff = sub(&minuend, &subtrahend);
                assert!(diff.is_some());

                assert_eq!(proof, diff.unwrap());
            }
        }
    }

    mod sub_shortcut {
        use crate::{nought_raw, sub_shortcut, Row};

        #[test]
        fn nought_subtrahend_test() {
            let minuend = Row::new_from_num(40);
            let subtrahend = nought_raw();

            let proof = minuend.clone();
            let test = sub_shortcut(&minuend.row, &subtrahend);
            assert_eq!(Some(Some(proof)), test);
        }

        #[test]
        fn lesser_minuend_test() {
            let minuend = Row::new_from_num(0).row;
            let subtrahend = Row::new_from_num(1).row;

            let res = sub_shortcut(&minuend, &subtrahend);
            assert_eq!(Some(None), res);
        }

        #[test]
        fn equal_operands_test() {
            let minuend = Row::new_from_num(1364).row;
            let subtrahend = Row::new_from_num(1364).row;

            let proof = Row::nought();
            let test = sub_shortcut(&minuend, &subtrahend);
            assert_eq!(Some(Some(proof)), test);
        }

        #[test]
        fn greater_minuend_test() {
            let minuend = Row::new_from_num(2).row;
            let subtrahend = Row::new_from_num(1).row;

            let res = sub_shortcut(&minuend, &subtrahend);
            assert_eq!(None, res);
        }
    }

    /// Multiplication.
    mod mul {
        use crate::{mul, Row};

        #[test]
        fn basic_test() {
            let row1 = Row::new_from_num(2);
            let row2 = Row::new_from_num(3);
            let prod = mul(&row1, &row2);
            assert_eq!(&[6], &*prod);
        }

        #[test]
        fn row1_nought_test() {
            let row1 = Row::nought();
            let row2 = Row::new_from_num(123456789_10111213);
            let prod = mul(&row1, &row2);
            let row = &prod.row;
            assert_eq!(&[0], row.as_slice());
            assert!(row.capacity() < row2.len());
        }

        #[test]
        fn row2_nought_test() {
            let row1 = Row::new_from_num(123456789_10111213);
            let row2 = Row::nought();
            let prod = mul(&row1, &row2);
            let row = &prod.row;
            assert_eq!(&[0], row.as_slice());
            assert!(row.capacity() < row1.len());
        }

        #[test]
        fn both_nought_test() {
            let row1 = Row::nought();
            let row2 = Row::nought();
            let prod = mul(&row1, &row2);
            assert_eq!(&[0], &*prod);
        }

        #[test]
        fn advanced_test() {
            let row = Row::new_from_num(u128::MAX);
            let prod = mul(&row, &row);
            let proof =
                "115792089237316195423570985008687907852589419931798687112530834793049593217025";
            assert_eq!(proof, prod.to_number());
        }
    }

    mod mul_shortcut {
        use crate::{mul_shortcut, nought_raw, unity_raw, Row};

        #[test]
        fn factor1_nought_test() {
            let row1 = nought_raw();
            let row2 = Row::new_from_num(333_990).row;

            let res = mul_shortcut(&row1, &row2);
            assert_eq!(Some(row1), res);
        }

        #[test]
        fn factor2_nought_test() {
            let row1 = Row::new_from_num(333_990).row;
            let row2 = nought_raw();

            let res = mul_shortcut(&row1, &row2);
            assert_eq!(Some(row2), res);
        }

        #[test]
        fn factor1_unity_test() {
            let row1 = unity_raw();
            let row2 = Row::new_from_num(333_990).row;

            let res = mul_shortcut(&row1, &row2);
            assert_eq!(Some(row2), res);
        }

        #[test]
        fn factor2_unity_test() {
            let row1 = Row::new_from_num(333_990).row;
            let row2 = unity_raw();

            let res = mul_shortcut(&row1, &row2);
            assert_eq!(Some(row1), res);
        }

        #[test]
        fn neither_unity_nor_nought_test() {
            let row = Row::new_from_num(2).row;

            let res = mul_shortcut(&row, &row);
            assert_eq!(None, res);
        }
    }

    /// For base ≥ 0 and exponent ≥ 0 power can be viewed as nothing more
    /// than repetetive multiplication with number in question.
    /// 0º=1, 0¹=1×0, 0²=1×0×0, 0³=1×0×0×0, …
    /// 1º=1, 1¹=1×1, 1²=1×1×1, 1³=1×1×1×1, …
    /// 2º=1, 2¹=1×2, 2²=1×2×2, 2³=1×2×2×2, …
    ///                   ⋮                   
    mod pow {
        use crate::{pow, Row};

        #[test]
        fn basic_test() {
            let row = Row::new_from_num(2);
            assert_eq!(&[4], &*pow(&row, 2));
        }

        #[test]
        fn advanced_test2() {
            let proof = Row::new_from_str("88817841970012523233890533447265625").unwrap();
            let row = Row::new_from_num(25);
            assert_eq!(proof, pow(&row, 25));
        }

        #[test]
        fn advanced_test3() {
            let proof = Row::new_from_str(
                "949279437109690919948053832937215463733689853138782229364504479870922851876864",
            )
            .unwrap();

            let row = Row::new_from_num(998);
            assert_eq!(proof, pow(&row, 26));
        }

        #[test]
        fn advanced_test4() {
            let proof = Row::new_from_str(
                "926336713898529563388567880069503262826159877325124512315660672063305037119488",
            )
            .unwrap();

            let row = Row::new_from_num(2);
            assert_eq!(proof, pow(&row, 259));
        }

        #[test]
        #[cfg(feature = "ext-tests")]
        // readme sample
        fn advanced_test5() {
            let row = Row::new_from_num(u128::MAX);
            let pow = pow(&row, 500);
            let number = pow.to_number();

            assert!(number.starts_with("8312324609993336522"));
            assert_eq!(19266, number.len());
        }

        #[test]
        fn zero_power_test() {
            let row = Row::new_from_num(0);
            let pow = pow(&row, 0);
            assert_eq!(&[1], &*pow);
        }

        #[test]
        fn one_power_test() {
            let row = Row::new_from_num(3030);
            let pow = pow(&row, 1);
            assert_eq!(&[0, 3, 0, 3], &*pow);
        }

        #[test]
        fn power_of_nought_test() {
            let row = Row::new_from_num(0);
            let pow = pow(&row, 1000);
            assert_eq!(&[0], &*pow);
        }

        #[test]
        fn power_of_one_test() {
            let row = Row::new_from_num(1);
            let pow = pow(&row, u16::MAX);
            assert_eq!(&[1], &*pow);
        }
    }

    mod pow_shortcut {
        use super::nought;
        use crate::{pow_shortcut, Row};

        #[test]
        fn zero_power_test() {
            let row = nought();
            let pow = pow_shortcut(&row, 0);
            assert_eq!(Some(Row::unity()), pow);
        }

        #[test]
        fn power_of_nought_test() {
            let row = Row::nought();
            let pow = pow_shortcut(&row.row, 1000);
            assert_eq!(Some(row), pow);
        }

        #[test]
        fn one_power_test() {
            let row = Row::new_from_num(3030);
            let pow = pow_shortcut(&row.row, 1);
            assert_eq!(Some(row), pow);
        }

        #[test]
        fn power_of_one_test() {
            let row = Row::unity();
            let pow = pow_shortcut(&row.row, u16::MAX);
            assert_eq!(Some(row), pow);
        }
    }

    /// Division with remainder.
    mod divrem {
        use crate::{divrem, Row};

        #[test]
        fn nought_divisor_test() {
            let dividend = Row::new_from_num(1);
            let divisor = Row::new_from_num(0);

            let ratrem = divrem(&dividend, &divisor);
            assert!(ratrem.is_none());
        }

        #[test]
        fn shorter_dividend_test() {
            let dividend = Row::new_from_num(99);
            let divisor = Row::new_from_num(999);

            let ratrem = divrem(&dividend, &divisor);
            assert!(ratrem.is_some());

            let ratrem = ratrem.unwrap();

            assert_eq!(Row::nought(), ratrem.0);
            assert_eq!(dividend, ratrem.1);
        }

        #[test]
        fn universal_test() {
            for quadruplet in [
                (0, 100, 0, 0),
                (99, 11, 9, 0),
                (133, 133, 1, 0),
                (90, 19, 4, 14),
                (700, 699, 1, 1),
                (700, 70, 10, 0),
            ] {
                let dividend = Row::new_from_num(quadruplet.0);
                let divisor = Row::new_from_num(quadruplet.1);

                let ratio = Row::new_from_num(quadruplet.2);
                let remainder = Row::new_from_num(quadruplet.3);
                let ratrem = divrem(&dividend, &divisor);

                assert!(ratrem.is_some());
                let ratrem = ratrem.unwrap();

                assert_eq!(ratio, ratrem.0);
                assert_eq!(remainder, ratrem.1);
            }
        }

        // readme sample
        #[test]
        fn load_test() {
            let dividend = Row::new_from_num(u128::MAX);
            let divisor = Row::new_from_num(249);

            let ratio = Row::new_from_num(1366595851088106278969375933460916511);
            let remainder = Row::new_from_num(216);

            let ratrem = divrem(&dividend, &divisor);
            assert_eq!(Some((ratio, remainder)), ratrem);
        }

        #[test]
        fn readme_sample_test() {
            let dividend =
                Row::new_from_str("3402823669209384634633746074317682114565556668744123").unwrap();
            let divisor =
                Row::new_from_str("14034568236692093846346337460345176821145655563453").unwrap();
            let ratio = "242";
            let remainder = "6458155929897923817932408914149323848308022388497";

            let ratrem = divrem(&dividend, &divisor).unwrap();

            assert_eq!(ratio, ratrem.0.to_number());
            assert_eq!(remainder, ratrem.1.to_number());
        }
    }

    mod divrem_shortcut {
        use crate::{divrem_shortcut, nought_raw, unity_raw, Row};

        #[test]
        fn nought_divisor_test() {
            let dividend = nought_raw();
            let divisor = nought_raw();

            let ratrem = divrem_shortcut(&dividend, &divisor);
            assert_eq!(Some(None), ratrem);
        }

        #[test]
        fn nought_dividend_test() {
            let dividend = nought_raw();
            let divisor = Row::new_from_num(4).row;

            let proof = (Row::nought(), Row::nought());
            let ratrem = divrem_shortcut(&dividend, &divisor);
            assert_eq!(Some(Some(proof)), ratrem);
        }

        #[test]
        fn unity_divisor_test() {
            let dividend = nought_raw();
            let divisor = unity_raw();

            let proof = (Row::nought(), Row::nought());
            let ratrem = divrem_shortcut(&dividend, &divisor);
            assert_eq!(Some(Some(proof)), ratrem);
        }

        #[test]
        fn unity_divisor_test2() {
            let dividend = Row::new_from_num(334_556);
            let divisor = unity_raw();

            let proof = (dividend.clone(), Row::nought());
            let ratrem = divrem_shortcut(&dividend.row, &divisor);
            assert_eq!(Some(Some(proof)), ratrem);
        }

        #[test]
        fn shorter_dividend_test() {
            let dividend = Row::new_from_num(99);
            let divisor = Row::new_from_num(999).row;

            let proof = (Row::nought(), dividend.clone());
            let ratrem = divrem_shortcut(&dividend.row, &divisor);
            assert_eq!(Some(Some(proof)), ratrem);
        }
    }

    mod divrem_acceleration {
        use crate::{divrem_acceleration, Row};
        use alloc::vec;

        #[test]
        fn basic_test() {
            let dividend = Row::new_from_num(65000);
            let divisor = vec![5];

            let mut w_ctr = 0;
            let mut ctr = 0;

            let ratio = Row::new_from_num(13_000).row;

            let remratio = divrem_acceleration(&dividend.row, &divisor, &mut w_ctr, &mut ctr);
            assert_eq!(vec![0], remratio.0);
            assert_eq!(ratio, remratio.1);

            assert_eq!(2, w_ctr);
            assert_eq!(7, ctr);

            // 65000 -1× 50000 ⇒ 1 +1
            // 15000 -3×  5000 ⇒ 3 +1
            // rem 0           ⇒ Σ 7 = 4 +2 +1
        }

        #[test]
        fn advanced_test1() {
            let dividend = Row::new_from_num(65535);
            let divisor = Row::new_from_num(277);

            let mut w_ctr = 0;
            let mut ctr = 0;

            let remratio = divrem_acceleration(&dividend.row, &divisor.row, &mut w_ctr, &mut ctr);

            assert_eq!(vec![3, 6, 1], remratio.0);
            assert_eq!(vec![6, 3, 2], remratio.1);

            assert_eq!(3, w_ctr);
            assert_eq!(15, ctr);

            // 65535 -2× 27700 ⇒ 2 +1
            // 10135 -3×  2770 ⇒ 3 +1
            // 1825  -6×   277 ⇒ 6 +1
            // rem 163         ⇒ Σ 15 = 11 +3 +1
        }

        #[test]
        fn advanced_test2() {
            let dividend = Row::new_from_num(65535);
            let divisor = vec![7, 2];

            let mut w_ctr = 0;
            let mut ctr = 0;

            let remratio = divrem_acceleration(&dividend.row, &divisor, &mut w_ctr, &mut ctr);

            assert_eq!(vec![6], remratio.0);
            assert_eq!(vec![7, 2, 4, 2], remratio.1);

            assert_eq!(4, w_ctr);
            assert_eq!(19, ctr);

            // 65535 -2× 27000 ⇒ 2 +1
            // 11535 -4×  2700 ⇒ 4 +1
            // 735   -2×   270 ⇒ 2 +1
            // 195   -7×    27 ⇒ 7 +1
            // rem 6           ⇒ Σ 19 = 15 +4 +0
        }

        #[test]
        fn advanced_test3() {
            let dividend = Row::new_from_num(99);
            let divisor = vec![5];

            let mut w_ctr = 0;
            let mut ctr = 0;

            let remratio = divrem_acceleration(&dividend.row, &divisor, &mut w_ctr, &mut ctr);

            assert_eq!(vec![4], remratio.0);
            assert_eq!(vec![9, 1], remratio.1);

            assert_eq!(2, w_ctr);
            assert_eq!(13, ctr);

            // 99 -1× 50 ⇒ 1 +1
            // 49 -9×  5 ⇒ 9 +1
            // rem 4     ⇒ Σ 13 = 10 +2 +1
        }

        #[test]
        fn advanced_test4() {
            let dividend = Row::new_from_num(65535);
            let divisor = Row::new_from_num(65536);

            let mut w_ctr = 0;
            let mut ctr = 0;

            let remratio = divrem_acceleration(&dividend.row, &divisor.row, &mut w_ctr, &mut ctr);

            assert_eq!(dividend.row, remratio.0);
            assert_eq!(vec![0], remratio.1);

            assert_eq!(0, w_ctr);
            assert_eq!(1, ctr);
            // rem 65535 ⇒ Σ 1 = 0 +1 (+0)
        }

        #[test]
        fn advanced_test5() {
            let num = &Row::new_from_num(65535).row;

            let mut w_ctr = 0;
            let mut ctr = 0;

            let remratio = divrem_acceleration(&num, &num, &mut w_ctr, &mut ctr);

            assert_eq!(vec![0], remratio.0);
            assert_eq!(vec![1], remratio.1);

            assert_eq!(0, w_ctr);
            assert_eq!(2, ctr);
            // 65535 -1× 65535 ⇒ 1 +1
            // rem 0           ⇒ Σ 2 = 1 +1 (+0)
        }

        #[test]
        fn advanced_test6() {
            let dividend = Row::new_from_num(60_000);
            let divisor = Row::new_from_num(6001); // cannot broaden up

            let mut w_ctr = 0;
            let mut ctr = 0;

            let remratio = divrem_acceleration(&dividend.row, &divisor.row, &mut w_ctr, &mut ctr);

            assert_eq!(vec![1, 9, 9, 5], remratio.0);
            assert_eq!(vec![9], remratio.1);

            assert_eq!(1, w_ctr);
            assert_eq!(11, ctr);

            // 60000 -9× 6001 ⇒ 9 +1
            // rem 5991       ⇒ Σ 11 = 9 +1 +1
        }

        #[test]
        fn advanced_test7() {
            let dividend = Row::new_from_num(111);
            let divisor = Row::new_from_num(1111);

            let mut w_ctr = 0;
            let mut ctr = 0;

            let remratio = divrem_acceleration(&dividend.row, &divisor.row, &mut w_ctr, &mut ctr);

            assert_eq!(dividend.row, remratio.0);
            assert_eq!(vec![0], remratio.1);

            assert_eq!(0, w_ctr);
            assert_eq!(0, ctr);
            // rem 111 ⇒ Σ 0
        }

        #[test]
        fn advanced_test8() {
            let dividend = Row::new_from_num(65535);
            let divisor = Row::new_from_num(6552);

            let mut w_ctr = 0;
            let mut ctr = 0;

            let remratio = divrem_acceleration(&dividend.row, &divisor.row, &mut w_ctr, &mut ctr);

            assert_eq!(vec![5, 1], remratio.0);
            assert_eq!(vec![0, 1], remratio.1);

            assert_eq!(1, w_ctr);
            assert_eq!(2, ctr);

            // 65535 -1× 65520 ⇒ 1 +1
            // rem 15          ⇒ Σ 2 = 1 +1 +0
        }

        #[test]
        fn advanced_test9() {
            let dividend = Row::new_from_num(65000);
            let divisor = Row::new_from_num(65);

            let mut w_ctr = 0;
            let mut ctr = 0;

            let remratio = divrem_acceleration(&dividend.row, &divisor.row, &mut w_ctr, &mut ctr);

            assert_eq!(vec![0], remratio.0);
            assert_eq!(vec![0, 0, 0, 1], remratio.1);

            assert_eq!(1, w_ctr);
            assert_eq!(2, ctr);

            // 65000 -1× 65000 ⇒ 1 +1
            // rem 0           ⇒ Σ 2 = 1 +1 +0
        }

        #[test]
        fn advanced_test10() {
            let dividend = Row::new_from_num(65001);
            let divisor = Row::new_from_num(65);

            let mut w_ctr = 0;
            let mut ctr = 0;

            let remratio = divrem_acceleration(&dividend.row, &divisor.row, &mut w_ctr, &mut ctr);

            assert_eq!(vec![1], remratio.0);
            assert_eq!(vec![0, 0, 0, 1], remratio.1);

            assert_eq!(1, w_ctr);
            assert_eq!(2, ctr);

            // 65001 -1× 65000 ⇒ 1 +1
            // rem 1           ⇒ Σ 2 = 1 +1 +0
        }

        #[test]
        fn advanced_test11() {
            let dividend = Row::new_from_num(60_000);
            let divisor = Row::new_from_num(700);

            let mut w_ctr = 0;
            let mut ctr = 0;

            let remratio = divrem_acceleration(&dividend.row, &divisor.row, &mut w_ctr, &mut ctr);

            assert_eq!(vec![0, 0, 5], remratio.0);
            assert_eq!(vec![5, 8], remratio.1);

            assert_eq!(2, w_ctr);
            assert_eq!(16, ctr);

            // 60000 -8× 7000 ⇒ 8 +1
            // 4000  -5×  700 ⇒ 5 +1
            // rem 500        ⇒ Σ 16 = 13 +2 +1
        }

        #[test]
        fn advanced_test12() {
            let dividend = Row::new_from_num(13990);
            let divisor = Row::new_from_num(130);

            let mut w_ctr = 0;
            let mut ctr = 0;

            let remratio = divrem_acceleration(&dividend.row, &divisor.row, &mut w_ctr, &mut ctr);

            assert_eq!(vec![0, 8], remratio.0);
            assert_eq!(vec![7, 0, 1], remratio.1);

            assert_eq!(1, w_ctr);
            assert_eq!(10, ctr);

            // 13990 -1× 13000 ⇒ 1 +1
            // 990   -7×   130 ⇒ 7 +1
            // rem 80          ⇒ Σ 10 = 8 +2 (+0)
        }

        #[test]
        fn load_test() {
            let dividend = Row::new_from_num(u128::MAX);
            let divisor = Row::new_from_num(249);

            let ratio = Row::new_from_num(1366595851088106278969375933460916511);

            let remratio = divrem_acceleration(&dividend.row, &divisor.row, &mut 0, &mut 0);

            assert_eq!(vec![6, 1, 2], remratio.0);
            assert_eq!(ratio.row, remratio.1);
        }
    }

    mod mulmul {
        use crate::{mulmul, Row};

        #[test]
        fn power_of_nought_test() {
            let row = Row::nought();
            let pow = mulmul(&row.row, &row.row, 1000 - 1);
            assert_eq!(row, pow);
        }

        #[test]
        #[cfg(feature = "one-power-mulmul-support")]
        fn one_power_test() {
            let row = Row::new_from_num(3030);
            let pow = mulmul(&row.row, &row.row, 1 - 1);
            assert_eq!(row, pow);
        }

        #[test]
        fn power_of_one_test() {
            let row = Row::unity();
            let pow = mulmul(&row.row, &row.row, u16::MAX - 1);
            assert_eq!(row, pow);
        }
    }

    /// Long multiplication fact notes:
    /// - When multiplying ones, maximum product is 81=9×9.
    /// - Thus maximum tens product is 8=⌊81÷10⌋.
    /// - Since 8+81=89 all results fit into 8=⌊89÷10⌋ tens.
    mod product {
        use crate::product as product_fn;
        use alloc::vec;
        use alloc::vec::Vec;

        #[test]
        fn basic_test() {
            let mcand = vec![3, 2, 1];
            let mpler = 3;
            let mut product = Vec::new();

            product_fn(mpler, &mcand, &mut product);

            assert_eq!(vec![9, 6, 3], product);
        }

        #[test]
        fn takeover_test() {
            let mcand = vec![9, 9, 9, 9, 9];
            let mpler = 9;
            let mut product = Vec::new();

            product_fn(mpler, &mcand, &mut product);

            assert_eq!(vec![1, 9, 9, 9, 9, 8], product);
        }
    }

    /// Column addition fact notes:
    /// - When adding ones, maximum sum is 18=9+9.
    /// - Thus maximum tens sum is 1=⌊18÷10⌋.
    /// - Since 18+1=19 any value fits into 1=⌊19÷10⌋ ten.
    mod addition {

        mod one_addend {
            use crate::addition;
            use alloc::vec;

            #[test]
            fn basic_test() {
                let ad1 = vec![4, 3, 2, 5];
                let mut sum = vec![1, 2, 3];

                addition(&ad1, None, &mut sum, 0);

                assert_eq!(vec![5, 5, 5, 5], sum);
            }

            #[test]
            fn takover_test() {
                let ad1 = vec![9];
                let mut sum = vec![9, 9, 9, 9, 9];

                addition(&ad1, None, &mut sum, 0);

                assert_eq!(vec![8, 0, 0, 0, 0, 1], sum);
            }

            #[test]
            fn longer_addition_test() {
                let ad1 = vec![8, 9, 9, 9, 9];
                let mut sum = vec![1, 1];

                addition(&ad1, None, &mut sum, 0);

                assert_eq!(vec![9, 0, 0, 0, 0, 1], sum);
            }

            #[test]
            fn offset_test() {
                let ad1 = vec![9, 9, 9, 9];
                let mut sum = vec![1, 1, 7, 8];

                addition(&ad1, None, &mut sum, 2);

                assert_eq!(vec![1, 1, 6, 8, 0, 0, 1], sum);
            }
        }

        mod two_addends {
            use crate::addition;
            use alloc::vec;
            use alloc::vec::Vec;

            #[test]
            fn basic_test() {
                let ad1 = vec![1, 1, 2, 4, 9];
                let ad2 = vec![8, 8, 7, 5];
                let mut sum = Vec::new();

                addition(&ad1, Some(&ad2), &mut sum, 0);

                assert_eq!(vec![9, 9, 9, 9, 9], sum);
            }

            #[test]
            fn takover_test() {
                let ad1 = vec![9];
                let ad2 = vec![9];
                let mut sum = Vec::new();

                addition(&ad1, Some(&ad2), &mut sum, 0);

                assert_eq!(vec![8, 1], sum);
            }

            #[test]
            fn longer_addition_test() {
                let ad1 = vec![8, 8, 9, 9, 9];
                let ad2 = vec![1, 1];
                let mut sum = Vec::new();

                addition(&ad1, Some(&ad2), &mut sum, 0);

                assert_eq!(vec![9, 9, 9, 9, 9], sum);
            }
        }
    }

    /// Column subtraction fact notes:
    /// - Subtrahend always must be lower or equal to minuend.
    /// - Minimum difference is 0=a-a, maximum 9=9-0=(9+a)-a, a ∈ [0;9].
    /// - Maximum subtrahend is 10=9+1(takeover).
    mod subtraction {

        mod subtracting {
            use crate::{subtraction, Row};
            use alloc::vec;

            #[test]
            fn basic_test() {
                let diffcount = subtraction(&vec![9, 9], &vec![0, 1], false, &mut 0);
                assert_eq!(&[9, 8], &*diffcount.0);
                assert_eq!(&[1], &*diffcount.1);
            }

            #[test]
            // minuend must be "copied" to difference if subtrahend is
            // exhausted
            fn minuend_copy_test() {
                let diffcount = subtraction(&vec![7, 7, 7], &vec![1], false, &mut 0);
                assert_eq!(&[6, 7, 7], &*diffcount.0);
                assert_eq!(&[1], &*diffcount.1);
            }

            #[test]
            fn advanced_test() {
                let minuend =
                    Row::new_from_str("6577102745386680762814942322444851025767571854389858533375")
                        .unwrap();
                let subtrahend =
                    Row::new_from_str("6296101835386680762814942322444851025767571854389858533376")
                        .unwrap();
                let proof =
                    Row::new_from_str("281000909999999999999999999999999999999999999999999999999")
                        .unwrap();

                let diffcount = subtraction(&minuend.row, &subtrahend.row, false, &mut 0);
                assert_eq!(proof.row, diffcount.0);
                assert_eq!(&[1], &*diffcount.1);
            }

            #[test]
            /// tests takeover ∈ [0,1] carry on
            fn takeover_test() {
                let diffcount = subtraction(&vec![8, 2, 2, 0, 1], &vec![9, 2, 1, 1], false, &mut 0);
                assert_eq!(&[9, 9, 0, 9], &*diffcount.0);
                assert_eq!(&[1], &*diffcount.1);
            }

            #[test]
            fn zero_truncation_test() {
                let diffcount = subtraction(&vec![9, 9, 9], &vec![8, 9, 9], false, &mut 0);
                let diff = diffcount.0;
                assert_eq!(&[1], &*diff);
                assert_eq!(&[1], &*diffcount.1);
                let diffcap = diff.capacity();
                assert!(1 == diffcap || diffcap < 3);
            }

            // because it can be
            // [1,0,9] - [2,0,9] = [9,9,9]
            // [9,9,9] + [2,0,9] = [1,0,9]
            // top place 9 must be preserved
            #[test]
            fn top_place_9_preservation_test() {
                let minuend = &vec![1, 0, 9];
                let subtrahend = vec![2, 0, 9];
                let diffcount = subtraction(minuend, &subtrahend, false, &mut 0);
                assert_eq!(minuend, &*diffcount.0);
                assert_eq!(&[0], &*diffcount.1);
            }

            // [1,1,1] - [3,4,7] = [8,6,3]
            // not user scenario, only internal expectation
            #[test]
            fn lesser_minuend_test() {
                let minuend = &vec![1, 1, 1];
                let subtrahend = vec![3, 4, 7];
                let diffcount = subtraction(minuend, &subtrahend, false, &mut 0);
                assert_eq!(minuend, &*diffcount.0);
                assert_eq!(&[0], &*diffcount.1);
            }
        }

        mod remainder {
            use crate::{subtraction, Row};
            use alloc::vec;

            #[test]
            fn basic_test() {
                let remratio = subtraction(&vec![3, 3], &vec![1, 1], true, &mut 0);
                assert_eq!(&[0], &*remratio.0);
                assert_eq!(&[3], &*remratio.1);
            }

            #[test]
            // minuend must be "copied" to remainder if subtrahend is
            // exhausted
            fn minuend_copy_test() {
                let remratio = subtraction(&vec![7, 7, 7], &vec![1], true, &mut 0);
                assert_eq!(&[0], &*remratio.0);
                assert_eq!(&[7, 7, 7], &*remratio.1);
            }

            #[test]
            fn remainder_test() {
                let remratio = subtraction(&vec![9], &vec![7], true, &mut 0);
                assert_eq!(&[2], &*remratio.0);
                assert_eq!(&[1], &*remratio.1);
            }

            #[test]
            fn takeover_test() {
                let remratio = subtraction(&vec![9, 0, 9], &vec![9], true, &mut 0);
                assert_eq!(&[0], &*remratio.0);
                assert_eq!(&[1, 0, 1], &*remratio.1);
            }

            #[test]
            // after invalid subtraction on remainder, places hold numbers resulting
            // from borrowing and subtracting
            // e.g. [2,0,0,0,0]-[7,7,3]=[5,2,6,9,9]:
            // - after remainder restoration [2,0,0,9,9],
            // - after `9`s truncation [2,0,0],
            // - after `0`s truncation [2]
            fn overrun_clearing_test() {
                let remratio = subtraction(&vec![2, 0, 0, 7, 7], &vec![7, 7], true, &mut 0);
                let remainder = remratio.0;
                assert_ne!(vec![5, 2, 9, 9, 9], remainder);
                assert_ne!(vec![2, 0, 9, 9, 9], remainder);
                assert_ne!(vec![2, 0], remainder);
                assert_eq!(vec![2], remainder);
                let remcap = remainder.capacity();
                assert!(1 == remcap || remcap < 5);
                assert_eq!(&[0, 0, 0, 1], &*remratio.1);
            }

            #[test]
            fn advanced_test() {
                let minuend = Row::new_from_num(627710173);
                let remainder = Row::new_from_num(130);
                let ratio = Row::new_from_num(1955483);

                let remratio = subtraction(&minuend.row, &vec![1, 2, 3], true, &mut 0);
                assert_eq!(&*remainder, &*remratio.0);
                assert_eq!(&*ratio, &*remratio.1);
            }

            #[test]
            fn advanced_test2() {
                let minuend = Row::new_from_num(627710173);
                let subtrahend = Row::new_from_num(3552741);
                let remainder = Row::new_from_num(2427757);
                let ratio = Row::new_from_num(176);

                let remratio = subtraction(&minuend.row, &subtrahend.row, true, &mut 0);
                assert_eq!(&*remainder, &*remratio.0);
                assert_eq!(&*ratio, &*remratio.1);
            }

            #[test]
            fn advanced_test3() {
                let minuend = Row::new_from_num(242775712);
                let subtrahend = Row::new_from_num(33333);
                let remainder = Row::new_from_num(11473);
                let ratio = Row::new_from_num(7283);

                let remratio = subtraction(&minuend.row, &subtrahend.row, true, &mut 0);
                assert_eq!(&*remainder, &*remratio.0);
                assert_eq!(&*ratio, &*remratio.1);
            }

            // because it can be
            // [1,0,9] - [2,0,9] = [9,9,9]
            // [9,9,9] + [2,0,9] = [1,0,9]
            // top place 9 must be preserved
            // 5411 = 5 ·902 +901
            #[test]
            fn top_place_9_preservation_test() {
                let minuend = vec![1, 1, 4, 5];
                let subtrahend = vec![2, 0, 9];
                let remratio = subtraction(&minuend, &subtrahend, true, &mut 0);
                assert_eq!(&[1, 0, 9], &*remratio.0);
                assert_eq!(&[5], &*remratio.1);
            }

            // [1,1,1] - [3,4,7] = [8,6,3]
            // implied by means of overrun correction
            #[test]
            fn lesser_dividend_test() {
                let dividend = &vec![1, 1, 1];
                let divisor = vec![3, 4, 7];
                let remratio = subtraction(dividend, &divisor, true, &mut 0);
                assert_eq!(dividend, &*remratio.0);
                assert_eq!(&[0], &*remratio.1);
            }

            // implied by means of overrun correction
            #[test]
            fn equal_operands_test() {
                let num = &vec![1, 1, 1];
                let remratio = subtraction(num, num, true, &mut 0);
                assert_eq!(&[0], &*remratio.0);
                assert_eq!(&[1], &*remratio.1);
            }

            #[test]
            #[cfg(feature = "shorter-dividend-support")]
            fn shorter_dividend_test() {
                let dividend = &vec![1, 1, 1];
                let divisor = vec![0, 4, 6, 8, 9, 3, 4, 7];
                let remratio = subtraction(dividend, &divisor, true, &mut 0);
                assert_eq!(dividend, &*remratio.0);
                assert_eq!(&[0], &*remratio.1);
            }
        }
    }

    /// Supporting method. Desinged to split ones from tens. Supports any range of tens.
    mod ones {
        use crate::ones;

        #[test]
        fn basic_test() {
            let num = 9;
            let mut takeover = 0;

            assert_eq!(9, ones(num, &mut takeover));
            assert_eq!(0, takeover);
        }

        #[test]
        fn split_test() {
            let num = 9;
            let mut takeover = 3;

            assert_eq!(2, ones(num, &mut takeover));
            assert_eq!(1, takeover);
        }

        #[test]
        fn maximum_test() {
            let num = 246;
            let mut takeover = 9;

            assert_eq!(5, ones(num, &mut takeover));
            assert_eq!(25, takeover);
        }
    }
}

// cargo test --features ext-tests --release

#![no_std]

extern crate alloc;

/// `PlacesRow` represents row of decimal places starting at ones (`0` index).
pub struct PlacesRow {
    row: Vec<u8>,
}

impl PlacesRow {
    /// Strong ctor for usage with prebuilded raw places row.
    ///
    /// Only ones are allowed in `row`.
    /// Places in `row` have to be ordered from ones over tens, hundreds, … to highest place;
    /// from 0-index to last-index.
    ///
    /// Leading zeros are truncated. Does not reallocate.
    ///
    /// Returns `PlacesRow` or index where place > `9` was
    /// encountered. `None` for 0-len `row`.
    pub fn new_from_vec(mut row: Vec<u8>) -> Result<Self, Option<usize>> {
        if row.len() == 0 {
            return Err(None);
        }

        let mut enumerator = row.iter().enumerate();
        while let Some((inx, num)) = enumerator.next() {
            let num = *num;
            if num > 9 {
                return Err(Some(inx));
            }
        }

        Self::truncate_leading_zeros_raw(&mut row);
        if 0 == row.len() {
            unsafe { row.set_len(1) }
        }

        Ok(PlacesRow { row })
    }

    /// Handy ctor for usage with _classic_ primitive numeric data type.
    pub fn new_from_num(num: u128) -> Self {
        PlacesRow {
            row: Self::from_num(num),
        }
    }

    fn from_num(mut num: u128) -> Vec<u8> {
        let mut row = Vec::new();
        loop {
            let d = num % 10;
            row.push(d as u8);
            num = num / 10;

            if num == 0 {
                break;
            }
        }

        row
    }

    /// Handy ctor for usage with long numbers.
    ///
    /// Only digits are allowed in `s`. Leading zeros are ommitted.        
    ///
    /// Returns `PlacesRow` or index in `s` where uncovertable `char` was
    /// encountered; `None` for empty string.
    pub fn new_from_str(s: &str) -> Result<Self, Option<usize>> {
        let row = Self::from_str(s, true);
        if let Err(e) = row {
            Err(e)
        } else {
            Ok(PlacesRow { row: row.unwrap() })
        }
    }

    fn from_str(s: &str, trim_zeroes: bool) -> Result<Vec<u8>, Option<usize>> {
        let s_len = s.len();
        if s_len == 0 {
            return Err(None);
        }

        let (s, s_len) = if trim_zeroes {
            let s = s.trim_start_matches('0');
            (s, s.len())
        } else {
            (s, s_len)
        };

        if s_len == 0 {
            return Ok(vec![0; 1]);
        }

        let mut row = Vec::with_capacity(s_len);
        let mut inx = s_len;

        for (c, mb) in s.chars().rev().zip(row.spare_capacity_mut()) {
            inx -= 1;
            if c.is_ascii_digit() {
                let d = c.to_digit(10).unwrap();
                mb.write(d as u8);
            } else {
                return Err(Some(inx));
            }
        }

        unsafe { row.set_len(s_len) }

        Ok(row)
    }

    /// Returns `String` representation.
    pub fn to_number(&self) -> String {
        let row = &self.row;
        let len = row.len();
        let mut number = String::with_capacity(len);
        for i in row.iter().rev() {
            let digit = match i {
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
                _ => panic!("Only ones supported."),
            };

            number.push(digit);
        }

        number
    }

    /// Truncates insignificant leading zeros.
    ///
    /// After certain operations, row can hold insignificant
    /// leading zeros. Use this to remove them.
    ///
    /// Does not alter current capacity. See `shrink_to_fit`.
    pub fn truncate_leading_zeros(&mut self) {
        Self::truncate_leading_zeros_raw(&mut self.row);
    }

    fn truncate_leading_zeros_raw(row: &mut Vec<u8>) {
        let trun = row.len() - Self::leading_zeros_raw(row);
        row.truncate(trun)
    }

    /// Calls `truncate_leading_zeros` and then tries to shrink to current len.
    pub fn shrink_to_fit(&mut self) {
        self.truncate_leading_zeros();
        self.row.shrink_to_fit();
    }

    /// Returns count of insignificant leading zeros.
    pub fn leading_zeros(&self) -> usize {
        Self::leading_zeros_raw(&self.row)
    }

    fn leading_zeros_raw(row: &Vec<u8>) -> usize {
        let mut count = 0;
        let mut rev = row.iter().rev();
        while let Some(num) = rev.next() {
            if *num == 0 as u8 {
                count += 1;
            } else {
                break;
            }
        }

        if row.len() == count {
            count - 1
        } else {
            count
        }
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
    // Converts `value` into `PlacesRow`.
    fn from(value: u128) -> Self {
        Self::new_from_num(value)
    }
}

use alloc::{string::String, vec, vec::Vec};

/// Computes `num1` and `num2` sum.
///
/// Returns `PlacesRow` with result.
pub fn add(num1: &PlacesRow, num2: &PlacesRow) -> PlacesRow {
    let places1 = &num1.row;
    let places2 = &num2.row;

    let (augend, addend) = if places1.len() > places2.len() {
        (places2, places1)
    } else {
        (places1, places2)
    };

    // avoids repetetive reallocations
    // +1 stands for contigent new place
    let mut sum = Vec::with_capacity(addend.len() + 1);

    #[cfg(test)]
    let sum_ptr = sum.as_ptr();

    addition(addend, Some(augend), &mut sum, 0);

    #[cfg(test)]
    assert!(sum_ptr == sum.as_ptr());

    PlacesRow { row: sum }
}

/// Computes `num1` and `num2` product.
///
/// Returns `PlacesRow` with result.
pub fn mul(num1: &PlacesRow, num2: &PlacesRow) -> PlacesRow {
    mulmul(&num1.row, &num2.row, 1)
}

/// Computes power `pow` of number `num`.
///
/// Potentially CPU, memory intesive.
///
/// Returns `PlacesRow` with result.
pub fn pow(num: &PlacesRow, pow: usize) -> PlacesRow {
    if pow == 0 {
        return PlacesRow { row: vec![1] };
    }

    let row = &num.row;
    mulmul(row, row, pow - 1)
}

/// Combined method allows to compute multiplication and power using shared code.
///
/// Not really efficient on power computation.
///   🡺 Inspect log₂ power speed up.
fn mulmul(row1: &Vec<u8>, row2: &Vec<u8>, times: usize) -> PlacesRow {
    let (mpler, mut mcand) = (row1, row2.clone());

    let mpler_len = mpler.len();

    // intermediate product of `mcand` and `mpler` place
    let mut i_product = Vec::with_capacity(0);
    // intermediate sum of intermediate products
    let mut i_sum = Vec::with_capacity(0);

    for _ in 0..times {
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

        mcand.clone_from(&i_sum);
        i_sum.clear();
    }

    PlacesRow { row: mcand }
}

/// Computes product of `mpler` and `mcand`.
fn product(mpler: u8, mcand: &Vec<u8>, product: &mut Vec<u8>) {
    let mut takeover = 0;
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
/// Precise expectations must be upkept when adding 2 addends: sum is assumed to be empty, `addend_1` to be longer (equal) of numbers and offset to be `0`.
fn addition(addend_1: &Vec<u8>, addend_2: Option<&Vec<u8>>, sum: &mut Vec<u8>, offset: usize) {
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

//precondition: minuend ≥ subtrahend ⇒ minuend.len() ≥ subtrahend.len()
fn substraction(minuend: &Vec<u8>, subtrahend: &Vec<u8>, modulo: bool) -> (Vec<u8>, Vec<u8>) {
    let mut diffmod_populated = false;

    let minuend_len = minuend.len();
    let subtrahend_len = subtrahend.len();

    let mut diffmod = vec![0; minuend_len];
    let diffmod_ptr = diffmod.as_ptr();
    let mut minuend_ptr = minuend.as_ptr();

    let mut ratio = vec![0; 1];
    let one = vec![1; 1];
    let mut takeover;
    let mut inx;
    loop {
        takeover = 0;
        inx = 0;

        while inx < minuend_len {
            let s_num = if inx < subtrahend_len {
                subtrahend[inx]
            } else if inx >= subtrahend_len && takeover == 0 && diffmod_populated {
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

            diffmod[inx] = m_num - total_s;
            inx += 1;
        }

        // existing remainder implies _minuend_ exhaustion
        // thus modulo is one turn more than is correct
        if takeover == 1 {
            inx = 0;
            takeover = 0;
            while inx < subtrahend_len {
                let correction = diffmod[inx] + subtrahend[inx];
                diffmod[inx] = ones(correction, &mut takeover);
                inx += 1;
            }

            while inx < minuend_len {
                diffmod[inx] = 0;
                inx += 1;
            }

            break;
        }

        addition(&one, None, &mut ratio, 0);

        if !modulo {
            break;
        }

        if !diffmod_populated {
            minuend_ptr = diffmod_ptr;
            diffmod_populated = true;
        }
    }

    (diffmod, ratio)
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

    mod placesrow {
        use crate::PlacesRow as Row;
        use alloc::string::ToString;
        use alloc::vec;
        use alloc::vec::Vec;

        mod new_from_vec {
            use crate::PlacesRow as Row;
            use alloc::vec;

            #[test]
            fn unsupported_num_test() {
                let row = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
                let row = Row::new_from_vec(row);

                assert!(row.is_err());
                assert_eq!(Some(10), row.err().unwrap());
            }

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
            fn zeros_reduction_test() {
                let row = Row::new_from_vec(vec![0, 0, 0]).unwrap();
                assert_eq!(&[0], &*row.row);
            }

            #[test]
            fn leading_zeros_trim_test() {
                let row = Row::new_from_vec(vec![1, 2, 0, 0]);                
                assert_eq!(&[1, 2], &*row.unwrap().row);
            }
        }

        #[test]
        fn new_from_num_test() {
            let row = Row::new_from_num(1234567890);
            assert_eq!(&[0, 9, 8, 7, 6, 5, 4, 3, 2, 1], &*row.row);
        }

        mod new_from_str {
            use crate::PlacesRow as Row;

            #[test]
            fn nondigit_str_test() {
                let row = Row::new_from_str("12w123");
                assert!(row.is_err());
                let inx = row.err().unwrap();
                assert!(inx.is_some());
                assert_eq!(2, inx.unwrap());
            }

            #[test]
            fn basic_test() {
                let row = Row::new_from_str("1234567890");
                assert!(row.is_ok());
                assert_eq!(&[0, 9, 8, 7, 6, 5, 4, 3, 2, 1], &*row.unwrap().row);
            }

            #[test]
            fn zeros_reduction_test() {
                let row = Row::new_from_str("0000");
                assert!(row.is_ok());
                assert_eq!(&[0], &*row.unwrap().row);
            }

            #[test]
            fn leading_zeros_trim_test() {
                let row = Row::new_from_str("0021");                
                assert_eq!(&[1, 2], &*row.unwrap().row);
            }

            #[test]
            fn zero_len_test() {
                let row = Row::new_from_str("");
                assert!(row.is_err());
                assert_eq!(None, row.err().unwrap());
            }
        }

        mod to_number {
            use crate::PlacesRow as Row;
            use alloc::vec;

            #[test]
            fn basic_test() {
                let row = Row::new_from_vec(vec![0, 9, 8, 7, 6, 5, 4, 3, 2, 1]).unwrap();
                assert_eq!("1234567890", row.to_number().as_str());
            }

            #[test]
            #[should_panic(expected = "Only ones supported.")]
            fn only_ones_supported_test() {
                let row = Row { row: vec![10] };
                _ = row.to_number();
            }
        }

        #[test]
        fn to_string_test() {
            let row = Row::new_from_num(1);
            assert_eq!("1", row.to_string());
        }

        #[test]
        fn truncate_leading_zeros_test() {
            let mut row = Row { row: vec![1, 2, 0] };
            row.truncate_leading_zeros();

            assert_eq!(&[1, 2], &*row.row);
        }

        #[test]
        fn shrink_to_fit_test() {
            let mut row = Vec::with_capacity(10);
            row.push(1);
            row.push(2);
            row.push(0);

            let mut row = Row { row };
            row.shrink_to_fit();
            assert_eq!(&[1, 2], &*row.row);
            assert_eq!(2, row.row.capacity());
        }

        mod leading_zeros {
            use crate::PlacesRow as Row;
            use alloc::vec;

            #[test]
            fn basic_test() {
                let row = Row { row: vec![1, 2, 0] };
                assert_eq!(1, row.leading_zeros());
            }

            #[test]
            fn zero_test() {
                let row = Row { row: vec![0, 0, 0] };
                assert_eq!(2, row.leading_zeros());
            }
        }
    }

    // Addition.
    mod add {
        use crate::{add, PlacesRow as Row};

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
            assert_eq!(Row::from_num(10_005), sum.row);
        }

        #[test]
        fn right_num_longer_test2() {
            let row1 = Row::new_from_num(5);
            let row2 = Row::new_from_num(10_000);

            let sum = add(&row1, &row2);
            assert_eq!(Row::from_num(10_005), sum.row);
        }

        #[test]
        fn advanced_test() {
            let row = Row::new_from_str("680564733841876926926749214863536422910").unwrap();

            let sum = add(&row, &row);
            let proof = Row::from_str("1361129467683753853853498429727072845820", false).unwrap();
            assert_eq!(proof, sum.row);
        }
    }

    /// Multiplication.
    mod mul {
        use crate::{mul, PlacesRow as Row};

        #[test]
        fn basic_test() {
            let row1 = Row::new_from_num(2);
            let row2 = Row::new_from_num(3);
            let mul = mul(&row1, &row2);
            assert_eq!(&[6], &*mul.row);
        }

        #[test]
        fn left_num_longer_test() {
            let row1 = Row::new_from_num(123456);
            let row2 = Row::new_from_num(2);
            let mul = mul(&row1, &row2);
            assert_eq!(&[2, 1, 9, 6, 4, 2], &*mul.row);
        }

        #[test]
        fn right_num_longer_test() {
            let row1 = Row::new_from_num(1);
            let row2 = Row::new_from_num(123456);
            let mul = mul(&row1, &row2);
            assert_eq!(&[6, 5, 4, 3, 2, 1], &*mul.row);
        }
        #[test]
        fn zero_num_test() {
            let row1 = Row::new_from_num(0);
            let row2 = Row::new_from_num(123456);
            let mul = mul(&row1, &row2);
            assert_eq!(&[0, 0, 0, 0, 0, 0], &*mul.row);
        }

        #[test]
        fn zero_nums_test() {
            let row1 = Row::new_from_num(0);
            let row2 = Row::new_from_num(0);
            let mul = mul(&row1, &row2);
            assert_eq!(&[0], &*mul.row);
        }

        #[test]
        fn advanced_test() {
            let row = Row::new_from_num(u128::MAX);
            let mul = mul(&row, &row);
            let proof = Row::from_str(
                "115792089237316195423570985008687907852589419931798687112530834793049593217025",
                false,
            )
            .unwrap();
            assert_eq!(proof, mul.row);
        }
    }

    /// For base ≥ 0 and exponent ≥ 0 power can be viewed as nothing more
    /// than repetetive multiplication with number in question.    
    /// E.g.: 0º=1, 0¹=1×0, 0²=1×0×0, 0³=1×0×0×0, …
    /// E.g.: 1º=1, 1¹=1×1, 1²=1×1×1, 1³=1×1×1×1, …
    /// E.g.: 2º=1, 2¹=1×2, 2²=1×2×2, 2³=1×2×2×2, …    
    ///                   ⋮
    mod pow {
        use crate::{pow, PlacesRow as Row};

        #[test]
        fn basic_test() {
            let row = Row::new_from_num(2);
            assert_eq!(&[4], &*pow(&row, 2).row);
        }

        #[test]
        fn advanced_test2() {
            let proof = Row::from_str("88817841970012523233890533447265625", false).unwrap();
            let row = Row::new_from_num(25);
            assert_eq!(proof, pow(&row, 25).row);
        }

        #[test]
        fn advanced_test3() {
            let proof = Row::from_str(
                "949279437109690919948053832937215463733689853138782229364504479870922851876864",
                false,
            )
            .unwrap();

            let row = Row::new_from_num(998);
            assert_eq!(proof, pow(&row, 26).row);
        }

        #[test]
        fn advanced_test4() {
            let proof = Row::from_str(
                "926336713898529563388567880069503262826159877325124512315660672063305037119488",
                false,
            )
            .unwrap();

            let row = Row::new_from_num(2);
            assert_eq!(proof, pow(&row, 259).row);
        }

        //#[test]
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
            assert_eq!(&[1], &*pow.row);
        }

        #[test]
        fn one_power_test() {
            let row = Row::new_from_num(3030);
            let pow = pow(&row, 1);
            assert_eq!(&[0, 3, 0, 3], &*pow.row);
        }

        #[test]
        fn power_of_zero_test_1() {
            let row = Row::new_from_num(0);
            let pow = pow(&row, 1000);
            assert_eq!(&[0], &*pow.row);
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
            let mcand = vec![3];
            let mpler = 3;
            let mut product = Vec::new();

            product_fn(mpler, &mcand, &mut product);

            assert_eq!(vec![9], product);
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
                let ad1 = vec![4, 3, 2, 1];
                let mut sum = vec![1, 2, 3, 4];

                addition(&ad1, None, &mut sum, 0);

                assert_eq!(vec![5, 5, 5, 5], sum);
            }

            #[test]
            fn takover_test() {
                let ad1 = vec![9, 9, 9, 9, 9];
                let mut sum = vec![9];

                addition(&ad1, None, &mut sum, 0);

                assert_eq!(vec![8, 0, 0, 0, 0, 1], sum);
            }

            #[test]
            fn longer_addition_test() {
                let ad1 = vec![9, 9, 9, 9, 9];
                let mut sum = vec![9, 9];

                addition(&ad1, None, &mut sum, 0);

                assert_eq!(vec![8, 9, 0, 0, 0, 1], sum);
            }

            #[test]
            fn offset_test_1() {
                let ad1 = vec![9, 9, 9, 9];
                let mut sum = vec![9, 9, 9, 9];

                addition(&ad1, None, &mut sum, 2);

                assert_eq!(vec![9, 9, 8, 9, 0, 0, 1], sum);
            }

            #[test]
            fn offset_test_2() {
                let ad1 = vec![9, 9];
                let mut sum = vec![9, 9, 9, 9];

                addition(&ad1, None, &mut sum, 2);

                assert_eq!(vec![9, 9, 8, 9, 1], sum);
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
                let ad1 = vec![9, 9, 9, 9, 9];
                let ad2 = vec![9, 9, 9, 9, 9];
                let mut sum = Vec::new();

                addition(&ad1, Some(&ad2), &mut sum, 0);

                assert_eq!(vec![8, 9, 9, 9, 9, 1], sum);
            }

            #[test]
            fn longer_addition_test() {
                let ad1 = vec![9, 9, 9, 9];
                let ad2 = vec![9, 9];
                let mut sum = Vec::new();

                addition(&ad1, Some(&ad2), &mut sum, 0);

                assert_eq!(vec![8, 9, 0, 0, 1], sum);
            }
        }
    }

    /// Column substraction fact notes:
    /// - Subtrahend always must be lower or equal to minuend.
    /// - Minimum difference is 0=a-a, maximum 9=9-0=(9+a)-a.
    /// - Maximum subtrahend is 10=9+1(takeover).
    mod substraction {

        mod substracting {
            use crate::{substraction, PlacesRow as Row};
            use alloc::vec;

            #[test]
            fn basic_test() {
                let result = substraction(&vec![9, 9], &vec![0, 1], false);
                assert_eq!(&[9, 8], &*result.0);
                assert_eq!(&[1], &*result.1);
            }

            #[test]
            // minuend must be "copied" to difference if subtrahend is
            // exhausted
            fn minuend_copy_test() {
                let result = substraction(&vec![9, 9, 9], &vec![1], false);
                assert_eq!(&[8, 9, 9], &*result.0);
                assert_eq!(&[1], &*result.1);
            }

            #[test]
            fn advanced_test() {
                let minuend = Row::from_str(
                    "6577102745386680762814942322444851025767571854389858533375",
                    false,
                )
                .unwrap();
                let subtrahend = Row::from_str(
                    "6296101835386680762814942322444851025767571854389858533376",
                    false,
                )
                .unwrap();
                let proof = Row::from_str(
                    "0281000909999999999999999999999999999999999999999999999999",
                    false,
                )
                .unwrap();

                let result = substraction(&minuend, &subtrahend, false);
                assert_eq!(proof, result.0);
                assert_eq!(&[1], &*result.1);
            }

            #[test]
            /// tests takeover ∈ [0,1] carry on            
            fn takeover_test() {
                let result = substraction(&vec![8, 2, 2, 2], &vec![9, 2, 1, 1], false);
                assert_eq!(&[9, 9, 0, 1], &*result.0);
                assert_eq!(&[1], &*result.1);
            }
        }

        mod modulo {
            use crate::{substraction, PlacesRow as Row};

            #[test]
            fn basic_test() {
                let result = substraction(&vec![3, 3], &vec![1, 1], true);
                assert_eq!(&[0, 0], &*result.0);
                assert_eq!(&[3], &*result.1);
            }

            #[test]
            fn modulo_test() {
                let result = substraction(&vec![6, 2], &vec![7], true);
                assert_eq!(&[5, 0], &*result.0);
                assert_eq!(&[3], &*result.1);
            }

            #[test]
            // after invalid substraction on modulo, places holds numbers resulting
            // from borrowing and substracting
            // e.g. [0,0,2,2]-[7,7]=[5,4,9,9], after modulo restore [2,2,9,9],
            // after clearing [2,2,0,0]
            // e.g. [0,0,0,0,3]-[7,2,1]=[6,7,8,9,9],[3,0,0,9,9],[3,0,0,0,0].
            fn overrun_clearing_test() {
                let result = substraction(&vec![7, 7, 1, 1], &vec![7, 7], true);
                assert_eq!(&[2, 2, 0, 0], &*result.0);
                assert_eq!(&[5, 1], &*result.1);
            }

            #[test]
            fn advanced_test() {
                let minuend = Row::from_str("627710173", false).unwrap();
                let modulo = Row::from_str("000000130", false).unwrap();
                let ratio = Row::from_str("1955483", false).unwrap();

                let result = substraction(&minuend, &vec![1, 2, 3], true);
                assert_eq!(&modulo, &*result.0);
                assert_eq!(&ratio, &*result.1);
            }

            #[test]
            fn advanced_test2() {
                let minuend = Row::from_str("627710173", false).unwrap();
                let subtrahend = Row::from_str("3552741", false).unwrap();
                let modulo = Row::from_str("002427757", false).unwrap();
                let ratio = Row::from_str("176", false).unwrap();

                let result = substraction(&minuend, &subtrahend, true);
                assert_eq!(&modulo, &*result.0);
                assert_eq!(&ratio, &*result.1);
            }

            #[test]
            fn advanced_test3() {
                let minuend = Row::from_str("242775712", false).unwrap();
                let subtrahend = Row::from_str("33333", false).unwrap();
                let modulo = Row::from_str("000011473", false).unwrap();
                let ratio = Row::from_str("7283", false).unwrap();

                let result = substraction(&minuend, &subtrahend, true);
                assert_eq!(&modulo, &*result.0);
                assert_eq!(&ratio, &*result.1);
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

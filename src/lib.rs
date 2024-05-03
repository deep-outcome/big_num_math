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
    /// Returns `PlacesRow` or index where place > `9` was
    /// encountered.
    pub fn new_from_vec(row: Vec<u8>) -> Result<Self, usize> {
        let mut enumerator = row.iter().enumerate();

        let mut zeros = 0;
        while let Some((inx, num)) = enumerator.next() {
            let num = *num;
            if num > 9 {
                return Err(inx);
            }

            if num == 0 {
                zeros += 1;
            }
        }

        Ok(PlacesRow {
            row: if zeros == row.len() { vec![0] } else { row },
        })
    }

    /// Handy ctor for usage with _classic_ primitive numeric data type.
    pub fn new_from_num(num: u128) -> Self {
        PlacesRow {
            row: to_raw_row_a(num),
        }
    }

    /// Handy ctor for usage with long numbers.
    ///
    /// Only digits are allowed in `s`.
    ///
    /// Returns `None` when `s` is uncovertable to `PlacesRow`.
    pub fn new_from_str(s: &str) -> Option<Self> {
        if let Some(pr) = to_raw_row_b(s) {
            Some(PlacesRow { row: pr })
        } else {
            None
        }
    }

    /// Returns `String` representation.
    pub fn to_number(&self) -> String {
        crate::to_number(&self.row)
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

/// Converts `num` into row of decimal places starting at ones.
fn to_raw_row_a(mut num: u128) -> Vec<u8> {
    let mut rr = Vec::new();
    loop {
        let d = num % 10;
        rr.push(d as u8);
        num = num / 10;

        if num == 0 {
            break;
        }
    }

    rr
}

/// Converts `s` into row of decimal places starting at ones or
/// fails on this.
fn to_raw_row_b(s: &str) -> Option<Vec<u8>> {
    let mut rr = vec![0u8; s.len()];
    for (c, p) in s.chars().rev().zip(rr.iter_mut()) {
        if c.is_ascii_digit() {
            let d = c.to_digit(10);
            *p = d.unwrap() as u8;
        } else {
            return None;
        }
    }

    Some(rr)
}

/// Converts `row` into `String` representation.
fn to_number(row: &Vec<u8>) -> String {
    let row_len = row.len();
    let mut number = String::with_capacity(row_len);
    let mut zeros = 0;
    for i in row.iter().rev() {
        let digit = match i {
            0 => {
                zeros += 1;
                '0'
            }
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

    if zeros == row_len {
        number.truncate(1);
    }

    number
}

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

    let mut sum = Vec::new();
    addition(addend, Some(augend), &mut sum, 0);

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
    // next alogorithms are more optimal when `mcand`
    // is longer number
    let (mpler, mut mcand) = if row1.len() > row2.len() {
        (row2, row1.clone())
    } else {
        (row1, row2.clone())
    };

    let mpler_len = mpler.len();

    // intermediate product of `mcand` and `mpler` place
    let mut i_product = Vec::new();
    // intermediate sum of intermediate products
    let mut i_sum = Vec::new();
    for _ in 0..times {
        // avoids repetetive reallocations
        // +1 stands for contigent new place
        i_product.reserve(mcand.len() + 1);

        for offset in 0..mpler_len {
            product(mpler[offset], &mcand, &mut i_product);
            addition(&i_product, None, &mut i_sum, offset);
            i_product.clear();
        }

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
/// Beware, `addend_1` len + `offset` must always be at least same as `sum` len when `sum` serves as `addend_2` or directly as `addend_2` len.
/// Beware, when `addend_2` is some, `offset` must be `0`.
fn addition(addend_1: &Vec<u8>, addend_2: Option<&Vec<u8>>, sum: &mut Vec<u8>, offset: usize) {
    #[cfg(test)]
    assert!((addend_2.is_some() && offset == 0) || addend_2.is_none());

    #[cfg(test)]
    assert!(
        (addend_2.is_some() && addend_1.len() >= addend_2.unwrap().len()) || addend_2.is_none()
    );

    #[cfg(test)]
    assert!((addend_2.is_none() && addend_1.len() + offset >= sum.len()) || addend_2.is_some());

    // avoids repetetive reallocations
    // +1 stands for contigent new place
    // reallocation would also break pointer to vector buffer
    // in case when `sum` serves as `addend_2`
    let new_min_len = addend_1.len() + offset;
    sum.reserve(new_min_len - sum.len() + 1);

    // pure overhead for `add`
    // only `mulmul` could benefit here since index bound checks can
    // be ommitted later in loop body, however
    // performance measurement is needed for optimal decision
    // sum.resize(new_min_len, 0);

    let (addend_2_ptr, addend_2_len) = if let Some(addend) = addend_2 {
        (addend.as_ptr(), addend.len())
    } else {
        (sum.as_ptr(), sum.len())
    };

    let mut takeover = 0;
    for addend_1_inx in 0..addend_1.len() {
        let addend_1_num = addend_1[addend_1_inx];
        let addend_2_inx = addend_1_inx + offset;

        let nums_sum = if addend_2_inx < addend_2_len {
            let addend_2_num = unsafe { addend_2_ptr.offset(addend_2_inx as isize).read() };
            addend_2_num + addend_1_num
        } else {
            addend_1_num
        };

        let add = ones(nums_sum, &mut takeover);
        if let Some(refer) = sum.get_mut(addend_2_inx) {
            *refer = add;
        } else {
            sum.push(add);
        }
    }

    if takeover != 0 {
        sum.push(takeover);
    }
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
        use crate::PlacesRow;
        use alloc::string::ToString;

        mod new_from_vec {
            use crate::PlacesRow;
            use alloc::vec;

            #[test]
            fn unsupported_num_test() {
                let rr = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
                let pr = PlacesRow::new_from_vec(rr);

                assert!(pr.is_err());
                assert_eq!(10, pr.err().unwrap());
            }

            #[test]
            fn basic_test() {
                let rr = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
                let proof = rr.clone();
                let pr = PlacesRow::new_from_vec(rr);

                assert!(pr.is_ok());
                assert_eq!(proof, pr.ok().unwrap().row);
            }

            #[test]
            fn zeros_reduction_test() {
                let pr = PlacesRow::new_from_vec(vec![0, 0, 0]).unwrap();
                assert_eq!(vec![0], pr.row);
            }
        }

        #[test]
        fn new_from_num_test() {
            let pr = PlacesRow::new_from_num(1);
            assert_eq!(&[1], &*pr.row);
        }

        #[test]
        fn new_from_str_test() {
            let pr = PlacesRow::new_from_str("1");
            assert!(pr.is_some());
            assert_eq!(&[1], &*pr.unwrap().row);
        }

        #[test]
        fn to_number_test() {
            let pr = PlacesRow::new_from_num(1);
            assert_eq!("1", pr.to_number());
        }

        #[test]
        fn to_string_test() {
            let pr = PlacesRow::new_from_num(1);
            assert_eq!("1", pr.to_string());
        }
    }

    mod conversions {
        use crate::to_raw_row_a;

        #[test]
        fn to_row_raw_a_test() {
            let num = 1234567890;
            let rr = to_raw_row_a(num);

            assert_eq!(&[0, 9, 8, 7, 6, 5, 4, 3, 2, 1], &*rr);
        }

        mod to_raw_row_b {
            use crate::to_raw_row_b;

            #[test]
            fn uncovertable_str_test() {
                let rr = to_raw_row_b("w");
                assert!(rr.is_none());
            }

            #[test]
            fn basic_test() {
                let rr = to_raw_row_b("1234567890");
                assert!(rr.is_some());
                assert_eq!(&[0, 9, 8, 7, 6, 5, 4, 3, 2, 1], &*rr.unwrap());
            }
        }

        mod to_number {
            use crate::to_number;
            use alloc::vec;

            #[test]
            fn basic_test() {
                let row = vec![0, 9, 8, 7, 6, 5, 4, 3, 2, 1];
                let num = to_number(&row);

                assert_eq!("1234567890", num.as_str());
            }

            #[test]
            fn zeros_reduction_test() {
                let row = vec![0, 0, 0, 0, 0, 0];
                let num = to_number(&row);

                assert_eq!("0", num.as_str());
            }

            #[test]
            #[should_panic(expected = "Only ones supported.")]
            fn only_ones_supported_test() {
                let row = vec![10];
                _ = to_number(&row);
            }
        }
    }

    // Addition.
    mod add {
        use crate::{add, to_raw_row_a, to_raw_row_b, PlacesRow};

        #[test]
        fn basic_test() {
            let pr1 = PlacesRow::new_from_num(4);
            let pr2 = PlacesRow::new_from_num(5);

            let sum = add(&pr1, &pr2);
            assert_eq!(&[9], &*sum.row);
        }

        #[test]
        fn left_num_longer_test() {
            let pr1 = PlacesRow::new_from_num(99_999);
            let pr2 = PlacesRow::new_from_num(5);

            let sum = add(&pr1, &pr2);
            assert_eq!(to_raw_row_a(100_004), sum.row);
        }

        #[test]
        fn right_num_longer_test() {
            let pr1 = PlacesRow::new_from_num(5);
            let pr2 = PlacesRow::new_from_num(99_999);

            let sum = add(&pr1, &pr2);
            assert_eq!(to_raw_row_a(100_004), sum.row);
        }

        #[test]
        fn advanced_test() {
            let pr = PlacesRow::new_from_str("680564733841876926926749214863536422910").unwrap();

            let sum = add(&pr, &pr);
            let proof = to_raw_row_b("1361129467683753853853498429727072845820").unwrap();
            assert_eq!(proof, sum.row);
        }
    }

    /// Multiplication.
    mod mul {
        use crate::{mul, to_raw_row_b, PlacesRow};

        #[test]
        fn basic_test() {
            let pr1 = PlacesRow::new_from_num(2);
            let pr2 = PlacesRow::new_from_num(3);
            let mul = mul(&pr1, &pr2);
            assert_eq!(&[6], &*mul.row);
        }

        #[test]
        fn left_num_longer_test() {
            let pr1 = PlacesRow::new_from_num(123456);
            let pr2 = PlacesRow::new_from_num(2);
            let mul = mul(&pr1, &pr2);
            assert_eq!(&[2, 1, 9, 6, 4, 2], &*mul.row);
        }

        #[test]
        fn right_num_longer_test() {
            let pr1 = PlacesRow::new_from_num(1);
            let pr2 = PlacesRow::new_from_num(123456);
            let mul = mul(&pr1, &pr2);
            assert_eq!(&[6, 5, 4, 3, 2, 1], &*mul.row);
        }
        #[test]
        fn zero_num_test() {
            let pr1 = PlacesRow::new_from_num(0);
            let pr2 = PlacesRow::new_from_num(123456);
            let mul = mul(&pr1, &pr2);
            assert_eq!(&[0, 0, 0, 0, 0, 0], &*mul.row);
        }

        #[test]
        fn zero_nums_test() {
            let pr1 = PlacesRow::new_from_num(0);
            let pr2 = PlacesRow::new_from_num(0);
            let mul = mul(&pr1, &pr2);
            assert_eq!(&[0], &*mul.row);
        }

        #[test]
        fn advanced_test() {
            let pr = PlacesRow::new_from_num(u128::MAX);
            let mul = mul(&pr, &pr);
            let proof = to_raw_row_b(
                "115792089237316195423570985008687907852589419931798687112530834793049593217025",
            )
            .unwrap();
            assert_eq!(proof, &*mul.row);
        }
    }

    /// Positive whole number power can be viewed as nothing more
    /// than repetetive multiplication with number in question.
    /// For other powers rules are different. 0 power = 1 for all numbers.
    /// Real number powers are not allowed thus not debated.
    /// E.g.: 0º=1, 0¹=1×0, 2²=1×0×0, 2³=1×0×0×0, …
    /// E.g.: 1º=1, 1¹=1×1, 1²=1×1×1, 1³=1×1×1×1, …
    /// E.g.: 2º=1, 2¹=1×2, 2²=1×2×2, 2³=1×2×2×2, …    
    mod pow {
        use crate::{pow, to_raw_row_b, PlacesRow};

        #[test]
        fn basic_test() {
            let pr = PlacesRow::new_from_num(2);
            assert_eq!(&[4], &*pow(&pr, 2).row);
        }

        #[test]
        fn advanced_test2() {
            let proof = to_raw_row_b("88817841970012523233890533447265625").unwrap();
            let pr = PlacesRow::new_from_num(25);
            assert_eq!(proof, pow(&pr, 25).row);
        }

        #[test]
        fn advanced_test3() {
            let proof = to_raw_row_b(
                "949279437109690919948053832937215463733689853138782229364504479870922851876864",
            )
            .unwrap();

            let pr = PlacesRow::new_from_num(998);
            assert_eq!(proof, pow(&pr, 26).row);
        }

        #[test]
        fn advanced_test4() {
            let proof = to_raw_row_b(
                "926336713898529563388567880069503262826159877325124512315660672063305037119488",
            )
            .unwrap();

            let pr = PlacesRow::new_from_num(2);
            assert_eq!(proof, pow(&pr, 259).row);
        }

        //#[test]
        fn advanced_test5() {
            let pr = PlacesRow::new_from_num(u128::MAX);
            let pow = pow(&pr, 500);
            let number = pow.to_number();

            assert!(number.starts_with("8312324609993336522"));
            assert_eq!(19266, number.len());
        }

        #[test]
        fn zero_power_test() {
            let pr = PlacesRow::new_from_num(0);
            let pow = pow(&pr, 0);
            assert_eq!(&[1], &*pow.row);
        }

        #[test]
        fn one_power_test() {
            let pr = PlacesRow::new_from_num(3030);
            let pow = pow(&pr, 1);
            assert_eq!(&[0, 3, 0, 3], &*pow.row);
        }

        #[test]
        fn power_of_zero_test_1() {
            let pr = PlacesRow::new_from_num(0);
            let pow = pow(&pr, 1000);
            assert_eq!(&[0], &*pow.row);
        }
    }

    /// How long multiplication works?
    /// - When multiplying ones, maximum product is 81=9×9.
    /// - Thus maximum tens product is 8=⌊81÷10⌋.    
    /// - Since 8+81=89 all results fit into 8=⌊89÷10⌋ tens.
    mod product {
        use crate::product;
        use alloc::vec;
        use alloc::vec::Vec;

        #[test]
        fn basic_test() {
            let mcand = vec![3];
            let mpler = 3;
            let mut result = Vec::new();

            product(mpler, &mcand, &mut result);

            assert_eq!(vec![9], result);
        }

        #[test]
        fn takeover_test() {
            let mcand = vec![9, 9, 9, 9, 9];
            let mpler = 9;
            let mut result = Vec::new();

            product(mpler, &mcand, &mut result);

            assert_eq!(vec![1, 9, 9, 9, 9, 8], result);
        }
    }

    /// How column addition works?
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
                let mut res = vec![1, 2, 3, 4];

                addition(&ad1, None, &mut res, 0);

                assert_eq!(vec![5, 5, 5, 5], res);
            }

            #[test]
            fn takover_test() {
                let ad1 = vec![9, 9, 9, 9, 9];
                let mut res = vec![9];

                addition(&ad1, None, &mut res, 0);

                assert_eq!(vec![8, 0, 0, 0, 0, 1], res);
            }

            #[test]
            fn longer_addition_test() {
                let ad1 = vec![9, 9, 9, 9, 9];
                let mut res = vec![9, 9];

                addition(&ad1, None, &mut res, 0);

                assert_eq!(vec![8, 9, 0, 0, 0, 1], res);
            }

            #[test]
            fn offset_test_1() {
                let ad1 = vec![9, 9, 9, 9];
                let mut res = vec![9, 9, 9, 9];

                addition(&ad1, None, &mut res, 2);

                assert_eq!(vec![9, 9, 8, 9, 0, 0, 1], res);
            }

            #[test]
            fn offset_test_2() {
                let ad1 = vec![9, 9];
                let mut res = vec![9, 9, 9, 9];

                addition(&ad1, None, &mut res, 2);

                assert_eq!(vec![9, 9, 8, 9, 1], res);
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
                let mut res = Vec::new();

                addition(&ad1, Some(&ad2), &mut res, 0);

                assert_eq!(vec![9, 9, 9, 9, 9], res);
            }

            #[test]
            fn takover_test() {
                let ad1 = vec![9, 9, 9, 9, 9];
                let ad2 = vec![9, 9, 9, 9, 9];
                let mut res = Vec::new();

                addition(&ad1, Some(&ad2), &mut res, 0);

                assert_eq!(vec![8, 9, 9, 9, 9, 1], res);
            }

            #[test]
            fn longer_addition_test() {
                let ad1 = vec![9, 9, 9, 9];
                let ad2 = vec![9, 9];
                let mut res = Vec::new();

                addition(&ad1, Some(&ad2), &mut res, 0);

                assert_eq!(vec![8, 9, 0, 0, 1], res);
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

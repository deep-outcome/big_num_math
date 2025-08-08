macro_rules! new_from_num_raw {
    ($n:expr) => {{
        let mut n = $n;
        let mut row = Vec::new();
        loop {
            let d = n % 10;
            row.push(d as u8);
            n = n / 10;

            if n == 0 {
                break;
            }
        }

        row
    }};
}

macro_rules! new_from_num {
    ($n:expr) => {{
        let row = new_from_num_raw!($n);
        Row { row }
    }};
}

macro_rules! try_into_num {
    ($r:expr,$t:ty,$esc:expr) => {{
        let mut n = <$t>::default();
        let mut ix = 0usize;
        let len = $r.len();

        let mut overflow = false;
        while ix < len {
            let place = $r[ix];
            if place == 0 {
                ix += 1;
                continue;
            }

            if let Some(p) = <$t>::checked_pow(10, ix as u32) {
                if let Some(m) = <$t>::checked_mul(p, place as $t) {
                    if let Some(a) = <$t>::checked_add(m, n) {
                        n = a;

                        ix += 1;
                        continue;
                    } else {
                        *$esc = 3;
                    }
                } else {
                    *$esc = 2;
                }
            } else {
                *$esc = 1;
            }

            overflow = true;
            break;
        }

        if overflow == true {
            None
        } else {
            Some(n)
        }
    }};
}

#[cfg(test)]
mod tests_of_units {
    use crate::Row;

    #[test]
    fn new_from_num_test() {
        let num = u128::MAX;
        let row = new_from_num!(num);
        let test = row.to_number();
        let proof = num.to_string();

        assert_eq!(proof, test);
    }

    mod try_into_num {
        use crate::add;
        use crate::Row;

        #[test]
        fn basic_test() {
            let num = u128::MAX;
            let row = Row::new_from_u128(num);

            let mut esc = 0;
            let test = try_into_num!(&row.row, u128, &mut esc);
            assert_eq!(Some(num), test);
            assert_eq!(0, esc);
        }

        #[test]
        fn add_overflow_test() {
            let num = u8::MAX;
            let mut row = new_from_num!(num);
            row = add(&row, &Row::unity());

            let mut esc = 0;
            let test = try_into_num!(&row.row, u8, &mut esc);
            assert_eq!(None, test);
            assert_eq!(3, esc);
        }

        #[test]
        fn mul_overflow_test() {
            let num = 300;
            let row = new_from_num!(num);

            let mut esc = 0;
            let test = try_into_num!(&row.row, u8, &mut esc);
            assert_eq!(None, test);
            assert_eq!(2, esc);
        }

        #[test]
        fn pow_overflow_test() {
            let num = 1000;
            let row = new_from_num!(num);

            let mut esc = 0;
            let test = try_into_num!(&row.row, u8, &mut esc);
            assert_eq!(None, test);
            assert_eq!(1, esc);
        }
    }
}

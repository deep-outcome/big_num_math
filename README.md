### BIG NUM MATH
Library for computations on large numbers.

- development notes: 
    1. no plan for new functions (goniometric, radix, …)
    2. upcoming optimizations (memory consumption, speed up on some computations, ergonomy, …)    
- functions only:
    - addition +substraction, 
    - multiplication +division
    - relation operators
    - order of magnitude
    - power

### Usage Samples

##### power

```rust
let row = PlacesRow::new_from_num(u128::MAX);
let pow = pow(&row, 500);
let number = pow.to_number();

assert!(number.starts_with("8312324609993336522"));
assert_eq!(19266, number.len());
```

##### division with remainder

```rust
let dividend = PlacesRow::new_from_str("3402823669209384634633746074317682114565556668744123").unwrap();
let divisor  = PlacesRow::new_from_str(  "14034568236692093846346337460345176821145655563453").unwrap();
let ratio = "242";        
let remainder = "6458155929897923817932408914149323848308022388497";
        
let ratrem = divrem(&dividend, &divisor).unwrap();
        
assert_eq!(ratio, ratrem.0.to_number());
assert_eq!(remainder, ratrem.1.to_number());
```

```rust
let dividend = Row::new_from_num(u128::MAX);
let divisor = Row::new_from_num(249);

let ratio = Row::new_from_num(1366595851088106278969375933460916511);
let remainder = Row::new_from_num(216);

let ratrem = divrem(&dividend, &divisor);
assert_eq!(Some((ratio, remainder)), ratrem);
```

##### decimal places relation

```rust
let number    = Row::new_from_str("1489754132134687989463132131").unwrap();
let comparand = Row::new_from_str(        "48645698946456531371").unwrap();
let decrel = rel_dec(&number, &comparand);

assert_eq!(RelDec::Greater((28, 20, 8)), decrel);
```

##### order of magnitude

```rust
let number_1 = PlacesRow::new_from_num(3162277660168379331998893544432);
let number_2 = PlacesRow::new_from_num(3162277660168379331998893544433);

assert_eq!(Oom::Precise(30), ord_of_mag(&number_1, OomKind::Strict));
assert_eq!(Oom::Precise(31), ord_of_mag(&number_2, OomKind::Strict));
assert_eq!(Oom::Precise(30), ord_of_mag(&number_2, OomKind::Loose));
```

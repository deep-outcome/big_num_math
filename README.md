### BIG NUM MATH
Library for computations on large numbers.

- Underdeveloped: 
    - No plan for new functions (goniometric, radix, …).
    - Plan for optimizations (memory + speed up on some computations).
- Primitive simple functions only: addition+substraction, multiplication+division, relation operator, power.


### Example Usage

```rust
use big_num_math::{pow, PlacesRow};

let row = PlacesRow::new_from_num(u128::MAX);
let pow = pow(&row, 500);
let number = pow.to_number();

assert!(number.starts_with("8312324609993336522"));
assert_eq!(19266, number.len());
```

module StructureTypes.Scalar

open FStar.Real
module R = FStar.Math.Sqrt

let num = real

let scalar_one = 1.0R
let scalar_zero = 0.0R

let scalar_is_pos a = a >. 0.0R

let scalar_one_pos a = ()
let scalar_pos_nnz a = ()

let scalar_mul a1 a2 = a1 *. a2
let scalar_mul_assoc a b c = ()
let scalar_mul_comm a b = ()

let scalar_div a1 a2 = a1 /. a2

let scalar_add a1 a2 = a1 +. a2
let scalar_add_comm a b = ()
let scalar_add_assoc a b c = ()
let scalar_mul_add_l a1 a2 a3 = ()

let scalar_sqrt a1 = R.sqrt_zero (); R.sqrt a1

let scalar_neg a1 = 0.0R -. a1

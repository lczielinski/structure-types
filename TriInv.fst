module TriInv

open Scalar
open Vector
open MatrixType
open Matrix
open Identity

(* triangular inverse function *)
#push-options "--split_queries always"
let rec triangular_inv (#n:pos) (l:unit_lower n)
    : r:unit_lower n { is_inverse l r } =
    match n with
    | 1 -> l
    | _ ->
        let c, o, l' = destruct_lower l in
        let l'_inv = triangular_inv l' in
        let b = neg (mat_vec_mul l'_inv c) in
        augment_lower l'_inv b one_const
#pop-options

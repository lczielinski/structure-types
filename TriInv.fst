module TriInv

open Vector
open Matrix
open Identity

(* triangular inverse function *)
#push-options "--split_queries always"
let rec triangular_inv (#n:pos) (l:unit_lower n)
    : r:unit_lower n { is_inverse l r } =
    match n with
    | 1 -> l
    | _ ->
        let c, l' = destruct_lower_unitdiag l in
        let l'_inv = triangular_inv l' in
        let b = neg (mat_vec_mul l'_inv c) in
        augment_lower_unitdiag l'_inv b
#pop-options

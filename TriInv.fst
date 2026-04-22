module TriInv

open Vector
open Matrix
open Identity

(* triangular inverse function *)
#push-options "--split_queries always"
let rec triangular_inv (#n:pos) (l:sq_mat n Lower UnitDiag)
    : r:sq_mat n Lower UnitDiag { is_inverse l r } =
    match n with
    | 1 -> l
    | _ ->
        let c, l' = destruct_lower_unitdiag l in
        let l'_inv = triangular_inv l' in
        mat_vec_mul_assoc l' l'_inv c;
        augment_lower_unitdiag l'_inv (neg (mat_vec_mul l'_inv c))
#pop-options
// try pattern matching

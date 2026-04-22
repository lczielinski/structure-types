module TriInv

open Vector
open Matrix
open Identity

(* triangular inverse function *)
#push-options "--split_queries always"
let rec triangular_inv (#n:pos) (l:sq_mat n Lower UnitDiag) 
    : r:sq_mat n Lower UnitDiag { is_inverse l r } =
    if n = 1 then begin
        one_by_one_is_identity l;
        l
    end else begin
        let n' : pos = n - 1 in
        assert (n == n' + 1);
        let l : sq_mat (n' + 1) Lower UnitDiag = l in 
        let c, l' = destruct_lower_unitdiag #n' l in
        let l'_inv = triangular_inv #n' l' in
        mat_vec_mul_assoc l' l'_inv c;
        augment_lower_unitdiag l'_inv (neg (mat_vec_mul l'_inv c))
    end
// try pattern matching
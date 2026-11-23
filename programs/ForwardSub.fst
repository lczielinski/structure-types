module ForwardSub

open StructureTypes.All

let rec forward_sub (#n:nat) (l:mat n{lower l /\ nnz_diag l}) (b:cvec n) :
    x:cvec n{mat_vec_mul l x == b} =
    match l with
    | MNil -> VNil
    | MCons a _ c l' ->
        let VCons b1 b' = b in
        let x1 = scalar_div b1 a in
        let target = vec_sub b' (vec_scalar_mul c x1) in
        let x' = forward_sub l' target in
        VCons x1 x'

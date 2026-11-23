module BackSub

open StructureTypes.All

let rec back_sub (#n:nat) (u:mat n{upper u /\ nnz_diag u}) (y:cvec n) :
    x:cvec n{mat_vec_mul u x == y} =
    match u with
    | MNil -> VNil
    | MCons a b _ u' ->
        let VCons y1 y' = y in
        let x' = back_sub u' y' in
        let x1 = scalar_div (scalar_sub y1 (vec_dot b x')) a in
        VCons x1 x'
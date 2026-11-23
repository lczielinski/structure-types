module TriSolve

open StructureTypes.All
open TriInv

let tri_solve (#n:nat) (l:mat n{unit_lower l}) (b:cvec n) :
    x:cvec n{mat_vec_mul l x == b} =
    let l_inv = tri_inv l in
    mat_vec_mul l_inv b
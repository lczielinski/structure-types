module LUSolve

open StructureTypes.All
open LU
open ForwardSub
open BackSub

let lu_solve (#n:nat) (a:mat n{spd a \/ row_sdd a}) (b:cvec n) :
    x:cvec n{mat_vec_mul a x == b} = 
    let (|l, u|) = lu a in
    let y = forward_sub l b in
    back_sub u y
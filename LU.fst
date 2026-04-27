module LU

open Scalar
open Vector
open MatrixType
open Matrix

let rec lu (#n:pos) (m:spd(n)) :
  l:unit_lower(n) & u:pos_upper(n) =
  magic()

    // if n = 1 then
    //     (coerce singleton_unit, coerce m)
    // else
    //     let (c, a, b, _) = destruct_nnzdiag #(n - 1) m in
    //     let s  = schur1 m in
    //     let (l, u) = lu (coerce s) in
    //     let d  = col_div c a in
    //     let l' = augment_lower_unitdiag l d in
    //     let u' = augment_upper_nnzdiag u a b in
    //     (l', u')
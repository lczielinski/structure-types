module LU

open Scalar
open Vector
open MatrixType
open Matrix

#push-options "--z3rlimit 100 --split_queries no"
let rec lu (#n:pos) (m:mat(n){spd m}) :
  l:mat(n){unit_lower l} & 
  u:mat(n){upper u /\ mat_mul l u == m} =
  match n with
  | 1 -> (|_id_mat #1, m|)
  | _ -> 
    let (|c, a, b, d|) = destruct m in
    let s = schur1 d c a b in
    let (|l, u|) = lu s in
    let lc = vec_scalar_div c a in
    let l' = augment l lc _one _zero_rvec in
    let u' = augment u _zero_cvec a b in
    (|l', u'|)
#pop-options
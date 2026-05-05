module Cholesky

open Scalar
open Vector
open MatrixType
open Matrix
open MatMul
open OneByOne

let rec cholesky (#n:pos) (m:mat n{spd m}) :
  l:mat n{lower l /\ pos_diag l /\ mat_mul l (transpose l) == m} =
  match n with
  | 1 -> build_mat (sqrt (extract m))
  | _ ->
      let (|c, a, b, d|) = destruct m in
      let l11 = sqrt a in
      let l21 = vec_scalar_div c l11 in
      let s = schur1 d c a b in
      let l = cholesky s in
      augment l l21 l11 _zero_rvec
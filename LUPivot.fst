module LUPivot

open Scalar
open Vector
open MatrixType
open Matrix
open MatMul
open OneByOne

assume val pivot : #n:pos{n >= 2} -> m:mat n{inv m} ->
  p':mat n{perm p'} & m':mat n{inv m' /\ top_left_nnz m' /\ mat_mul p' m' == m}

let rec lu_pivoting (#n:pos) (m:mat n{inv m}) :
  p:mat n{perm p} &
  l:mat n{unit_lower l} &
  u:mat n{upper u /\ nnz_diag u /\ mat_mul p m == mat_mul l u} =
  match n with
  | 1 -> (|_id_mat, _id_mat, m|)
  | _ ->
    let (|p', m'|) = pivot m in
    let (|c, a, b, d|) = destruct m' in
    let s = schur1 d c a b in
    let (|p, l, u|) = lu_pivoting s in

    let lc = vec_scalar_div c a in
    let pd = mat_vec_mul p lc in
    let l' = augment l pd _one _zero_rvec in
    let u' = augment u _zero_cvec a b in
    let p_aug = augment p _zero_cvec _one _zero_rvec in
    let p'' = mat_mul p_aug (transpose p') in
    // explicit call: (p_aug * (transpose p')) * m == p_aug * ((transpose p') * m)
    mat_mul_assoc p_aug (transpose p') m;

    (|p'', l', u'|)

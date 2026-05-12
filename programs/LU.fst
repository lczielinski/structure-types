module LU

open All

let rec lu (#n:pos) (m:mat n{rowsdd m \/ spd m}) :
  l:mat n{unit_lower l} &
  u:mat n{upper u /\ nnz_diag u /\ mat_mul l u == m} =
  match m with
  | Mat1 a -> (|id_mat, m|)
  | MatN d c a b ->
    let s = schur1 d c a b in
    let (|l, u|) = lu s in
    let lc = vec_scalar_div c a in
    let l' = MatN l lc one zero_rvec in
    let u' = MatN u zero_cvec a b in
    (|l', u'|)
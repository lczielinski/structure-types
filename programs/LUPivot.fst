module LUPivot

open All

assume val pivot : #n:pos{n >= 2} -> m:mat n{inv m} ->
  p':mat n{perm p'} & m':mat n{inv m' /\ top_left_nnz m' /\ mat_mul p' m' == m}

let rec lu_pivoting (#n:pos) (m:mat n{inv m}) :
  p:mat n{perm p} & l:mat n{unit_lower l} &
  u:mat n{upper u /\ nnz_diag u /\ mat_mul p m == mat_mul l u} =
  match m with 
  | Mat1 a -> (|id_mat, id_mat, m|)
  | MatN _ _ _ _ ->
    let (|p', m'|) = pivot m in
    let MatN _ c a b = m' in
    let s = schur1 m' in
    let (|p, l, u|) = lu_pivoting s in

    let lc = vec_scalar_div c a in
    let pd = mat_vec_mul p lc in
    let l' = MatN l pd one zero_rvec in
    let u' = MatN u zero_cvec a b in
    let p_aug = MatN p zero_cvec one zero_rvec in
    let p'' = mat_mul p_aug (transpose p') in

    assert (mat_mul p_aug m' == mat_mul l' u');

    (|p'', l', u'|)

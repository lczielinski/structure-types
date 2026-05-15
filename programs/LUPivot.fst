module LUPivot

open All

assume val pivot : #n:pos{n >= 2} -> m:mat n{inv m} ->
  p':mat n{perm p'} & m':mat n{inv m' /\ top_left_nnz m' /\ mat_mul p' m' == m}

// assume val pivot_inverse : #n:pos -> p:mat n -> m:mat n -> m':mat n ->
//   Lemma (requires perm p /\ mat_mul p m' == m)
//         (ensures  mat_mul (transpose p) m == m')
//         [SMTPat (mat_mul (transpose p) m)]

#push-options "--split_queries always"
let rec lu_pivoting (#n:pos) (m:mat n{inv m}) :
  p:mat n{perm p} & l:mat n{unit_lower l} &
  u:mat n{upper u /\ nnz_diag u /\ mat_mul p m == mat_mul l u} =
  match m with
  | Mat1 _ -> (|_id_mat, _id_mat, m|)
  | MatN mm mb ma mc ->
    let (|p', m'|) = pivot m in
    let (MatN d c a b) = m' in
    let s = schur1 d c a b in
    let (|p, l, u|) = lu_pivoting s in

    let lc = vec_scalar_div c a in
    let pd = mat_vec_mul p lc in
    let l' = MatN l pd one zero_rvec in
    let u' = MatN u zero_cvec a b in
    let p_aug = MatN p zero_cvec one zero_rvec in
    let p'' = mat_mul p_aug (transpose p') in

    // assert (mat_mul (transpose p') m == m');
    (|p'', l', u'|)
#pop-options

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
    let MatN d c a b = m' in
    let s = schur1 d c a b in
    let (|p, l, u|) = lu_pivoting s in

    let lc = vec_scalar_div c a in
    let pd = mat_vec_mul p lc in
    let l' = MatN l pd one zero_rvec in
    let u' = MatN u zero_cvec a b in
    let p_aug = MatN p zero_cvec one zero_rvec in
    let p'' = mat_mul p_aug (transpose p') in

//     // perm_inv_l SMTPat needs literal mat_mul p' m' in second arg position;
//     // mat_mul p' m' == m (from pivot), so both assertions follow
//     assert (mat_mul (transpose p') (mat_mul p' m') == m');
//     assert (mat_mul (transpose p') m == m');
//     // mat_mul_assoc SMTPat needs literal mat_mul (mat_mul p_aug (transpose p')) m,
//     // not mat_mul p'' m — p'' is a let binding, a distinct E-graph node
//     assert (mat_mul (mat_mul p_aug (transpose p')) m == mat_mul p_aug m');
//     assert (mat_mul p'' m == mat_mul p_aug m');

//     // create term mat_vec_mul p (vec_scalar_mul lc a) so mat_vec_mul_scalar SMTPat fires:
//     //   mat_vec_mul p (vec_scalar_mul lc a) == vec_scalar_mul (mat_vec_mul p lc) a = vec_scalar_mul pd a
//     // combined with lc * a == c (vec_scalar_div_mul), gives vec_scalar_mul pd a == mat_vec_mul p c
//     assert (mat_vec_mul p (vec_scalar_mul lc a) == mat_vec_mul p c);
//     assert (vec_scalar_mul pd a == mat_vec_mul p c);

//     assert (mat_mul p s == mat_mul l u);
//     // s = mat_sub d (outer_prod lc b) by definition of schur1, but s is a let-binding so
//     // mat_mul_sub_distr won't fire on mat_mul p s — need the literal expanded form:
//     assert (mat_mul p (mat_sub d (outer_prod lc b)) == mat_sub (mat_mul p d) (outer_prod pd b));
//     // mat_mul_sub_distr fires on mat_mul p (mat_sub d (outer_prod lc b))
//     // mat_mul_outer_prod fires on mat_mul p (outer_prod lc b) => outer_prod pd b
//     // now mat_add_sub_cancel can close the top-left block:
//     //   mat_add (outer_prod pd b) (mat_sub (mat_mul p d) (outer_prod pd b)) == mat_mul p d
//     assert (mat_mul p_aug m' == mat_mul l' u');

//     (|p'', l', u'|)
  
    magic()

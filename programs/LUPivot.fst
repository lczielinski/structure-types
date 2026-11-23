module LUPivot

open StructureTypes.All

assume val pivot : #n:pos -> m:mat n{inv m} ->
  p':mat n{perm p'} & m':mat n{inv m' /\ top_left_nnz m' /\ mat_mul p' m' == m}

let rec lu_pivoting (#n:nat) (m:mat n{inv m}) :
  p:mat n{perm p} & l:mat n{unit_lower l} &
  u:mat n{upper u /\ nnz_diag u /\ mat_mul p m == mat_mul l u} =
  match m with
  | MNil -> (|id_mat, id_mat, m|)
  | MCons _ _ _ _ ->
    let (|p', m'|) = pivot m in
    let MCons a b c _ = m' in
    let s = schur1 m' in
    let (|p, l, u|) = lu_pivoting s in

    let lc = vec_scalar_div c a in
    let pd = mat_vec_mul p lc in
    let l' = MCons one zero_vec pd l in
    let u' = MCons a b zero_vec u in
    let p_aug = MCons one zero_vec zero_vec p in
    let p'' = mat_mul p_aug (transpose p') in

    (|p'', l', u'|)

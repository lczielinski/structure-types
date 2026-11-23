module LUPivot

open StructureTypes.All

assume val pivot : #n:pos -> m:mat n{invertible m} ->
  p':mat n{permutation p'} & m':mat n{invertible m' /\ top_left_nnz m' /\ mat_mul p' m' == m}

let rec lu_pivot (#n:nat) (m:mat n{invertible m}) :
  p:mat n{permutation p} & l:mat n{unit_lower l} &
  u:mat n{upper u /\ nnz_diag u /\ mat_mul p m == mat_mul l u} =
  match m with
  | MNil -> (|mat_id, mat_id, m|)
  | MCons _ _ _ _ ->
    let (|p', m'|) = pivot m in
    let MCons a b c _ = m' in
    let s = mat_schur m' in
    let (|p, l, u|) = lu_pivot s in

    let lc = vec_scalar_div c a in
    let pd = mat_vec_mul p lc in
    let l' = MCons scalar_one vec_zero pd l in
    let u' = MCons a b vec_zero u in
    let p_aug = MCons scalar_one vec_zero vec_zero p in
    let p'' = mat_mul p_aug (mat_transpose p') in

    (|p'', l', u'|)

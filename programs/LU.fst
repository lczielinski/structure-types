module LU

open StructureTypes.All

let rec lu (#n:nat) (m:mat n{row_sdd m \/ spd m}) :
  l:mat n{unit_lower l} &
  u:mat n{upper u /\ nnz_diag u /\ mat_mul l u == m} =
  match m with
  | MNil -> (|MNil, MNil|)
  | MCons a b c _ ->
    let s = mat_schur m in
    let (|l, u|) = lu s in
    let lc = vec_scalar_div c a in
    let l' = MCons scalar_one vec_zero lc l in
    let u' = MCons a b vec_zero u in
    (|l', u'|)

module LU

open StructureTypes.All

let rec lu (#n:nat) (m:mat n{rowsdd m \/ spd m}) :
  l:mat n{unit_lower l} &
  u:mat n{upper u /\ nnz_diag u /\ mat_mul l u == m} =
  match m with
  | MNil -> (|MNil, MNil|)
  | MCons a b c _ ->
    let s = schur1 m in
    let (|l, u|) = lu s in
    let lc = vec_scalar_div c a in
    let l' = MCons one zero_vec lc l in
    let u' = MCons a b zero_vec u in
    (|l', u'|)

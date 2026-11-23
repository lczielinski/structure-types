module Cholesky

open StructureTypes.All

let rec cholesky (#n:nat) (m:mat n{spd m}) :
  l:mat n{lower l /\ pos_diag l /\ mat_mul l (transpose l) == m} =
  match m with
  | MNil -> MNil
  | MCons a _ c _ ->
      let l11 = sqrt a in
      let l21 = vec_scalar_div c l11 in
      let s = schur1 m in
      let l = cholesky s in
      MCons l11 zero_vec l21 l

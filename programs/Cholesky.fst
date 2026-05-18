module Cholesky

open All

assume val spd_mat1_pos : a:num ->
  Lemma (requires spd (Mat1 a)) (ensures is_pos a) [SMTPat (spd (Mat1 a))]


let rec cholesky (#n:pos) (m:mat n{spd m}) :
  l:mat n{lower l /\ pos_diag l /\ mat_mul l (transpose l) == m} =
  match m with
  | Mat1 a -> 
    Mat1 (sqrt a)
  | MatN d c a b ->
      let l11 = sqrt a in
      let l21 = vec_scalar_div c l11 in
      let s = schur1 d c a b in
      let l = cholesky s in
      MatN l l21 l11 zero_rvec
module TriInv

open Vector
open Scalar
open Matrix
open MatrixType
open MatMul
open OneByOne

(* triangular inverse function *)
#push-options "--split_queries always"
let rec triangular_inv (#n:pos) (l:mat n{unit_lower l}) :
  r:mat n{unit_lower r /\ is_inverse l r} =
  match l with 
  | Mat1 a -> l
  | MatN l' c _ _ ->
    let l'_inv = triangular_inv l' in
    let b = vec_neg (mat_vec_mul l'_inv c) in
    MatN l'_inv b one zero_rvec
#pop-options

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
    // assert (mat_mul l' u' == m);
    (|l', magic()|)

let solve (#n:pos) (l:mat n{unit_lower l}) (b:cvec n) : 
    x:cvec n{mat_vec_mul l x == b} =
    let l_inv = triangular_inv l in
    mat_vec_mul l_inv b

let rec cholesky (#n:pos) (m:mat n{spd m}) :
  l:mat n{lower l /\ pos_diag l /\ mat_mul l (transpose l) == m} =
  match m with 
  | Mat1 a -> 
    assert (pos_diag m); 
    Mat1 (sqrt a)
  | MatN d c a b -> 
    let l11 = sqrt a in
    let l21 = vec_scalar_div c l11 in
    let s = schur1 d c a b in
    let l = cholesky s in
    let l' = MatN l l21 l11 zero_rvec in
    magic()

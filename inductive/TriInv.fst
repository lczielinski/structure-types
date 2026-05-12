module TriInv

open Vector
open Scalar
open Matrix
open MatrixType
open MatMul

(* triangular inverse function *)
#push-options "--split_queries always"
let rec triangular_inv (#n:pos) (l:mat n{unit_lower l}) :
  r:mat n{unit_lower r /\ is_inverse l r} =
  match l with
  | Mat1 a -> l
  | MatN l' c _ _ ->
    // assert (lower l' /\ unit_diag l');  // from unit_lower l
    let l'_inv = triangular_inv l' in
    // assert (mat_mul l'_inv l' == id_mat);   // from is_inverse l' l'_inv
    // assert (mat_mul l' l'_inv == id_mat);
    let b = vec_neg (mat_vec_mul l'_inv c) in
    let r = MatN l'_inv b one zero_rvec in
    // assert (unit_lower r);
    // block-formula steps for mat_mul r l == id_mat:
    //   top-left: mat_add (outer_prod b zero_rvec) (mat_mul l'_inv l') == id_mat
    //   col:      vec_add b (mat_vec_mul l'_inv c) == zero_cvec  [vec_neg_add_inv_l]
    //   corner:   scalar_add (scalar_mul one one) (inner_prod zero_rvec c) == one
    //   row:      vec_add (vec_scalar_mul zero_rvec one) (vec_mat_mul zero_rvec l') == zero_rvec
    // assert (mat_mul r l == id_mat);
    // block-formula steps for mat_mul l r == id_mat:
    //   col: vec_add c (mat_vec_mul l' b)
    //      = vec_add c (vec_neg (mat_vec_mul (mat_mul l' l'_inv) c))  [mat_vec_mul_vec_neg, mat_vec_mul_assoc]
    //      = vec_add c (vec_neg c)  [mat_mul l' l'_inv == id_mat, is_id => x == x]
    //      = zero_cvec  [vec_neg_add_inv_r]
    // assert (mat_mul l r == id_mat);
    r
#pop-options

let rec lu (#n:pos) (m:mat n{rowsdd m \/ spd m}) :
  l:mat n{unit_lower l} &
  u:mat n{upper u /\ nnz_diag u /\ mat_mul l u == m} =
  match m with
  | Mat1 a -> (|id_mat, m|)
  | MatN d c a b ->
    // assert (nnz_diag m);
    let s = schur1 d c a b in
    let (|l, u|) = lu s in
    let lc = vec_scalar_div c a in
    let l' = MatN l lc one zero_rvec in
    let u' = MatN u zero_cvec a b in
    // assert (mat_mul l u == s);
    // block-formula for mat_mul l' u' == MatN d c a b:
    //   top-left: mat_add (outer_prod lc b) (mat_mul l u) == d
    //             = mat_add (outer_prod lc b) s == d
    //             since s = mat_sub d (outer_prod lc b), need: v + (m - v) == m
    // assert (mat_add (outer_prod lc b) s == d);        // MISSING: mat_add_sub_cancel
    //   col: vec_scalar_mul lc a == c
    //        need: (vec_scalar_div c a) * a == c
    // assert (vec_scalar_mul lc a == c);                // MISSING: vec_scalar_div_mul
    // assert (mat_mul l' u' == m);
    (|l', u'|)

let solve (#n:pos) (l:mat n{unit_lower l}) (b:cvec n) :
    x:cvec n{mat_vec_mul l x == b} =
    let l_inv = triangular_inv l in
    // assert (mat_mul l l_inv == id_mat);
    // mat_vec_mul_assoc fires on: mat_vec_mul l (mat_vec_mul l_inv b)
    //   => mat_vec_mul (mat_mul l l_inv) b == mat_vec_mul id_mat b == b
    // assert (mat_vec_mul (mat_mul l l_inv) b == b);
    mat_vec_mul l_inv b

let rec cholesky (#n:pos) (m:mat n{spd m}) :
  l:mat n{lower l /\ pos_diag l /\ mat_mul l (transpose l) == m} =
  match m with
  | Mat1 a ->
    assert (pos_diag m);
    Mat1 (sqrt a)
  | MatN d c a b ->
    let l11 = sqrt a in   // is_pos a from destruct_spd, so l11 well-typed
    let l21 = vec_scalar_div c l11 in
    let s = schur1 d c a b in
    let l = cholesky s in
    let l' = MatN l l21 l11 zero_rvec in
    // assert (lower l');        // lower l (recursive) /\ is_zero_vec zero_rvec
    // assert (is_pos l11);      // from sqrt refinement: is_pos a ==> is_pos (sqrt a)
    // assert (pos_diag l');
    // block-formula for mat_mul l' (transpose l') == MatN d c a b:
    //   transpose l' = MatN (transpose l) (vec_trans zero_rvec) l11 (vec_trans l21)
    //                = MatN (transpose l) zero_cvec l11 (vec_trans l21)  [vec_trans_zero]
    // assert (scalar_mul l11 l11 == a);        // from sqrt refinement: a2*a2 == a1
    //   col: vec_scalar_mul l21 l11 == c
    //        need: (vec_scalar_div c l11) * l11 == c
    // assert (vec_scalar_mul l21 l11 == c);    // MISSING: vec_scalar_div_mul
    //   spd ==> symmetric ==> MatN d c a b == transpose (MatN d c a b)
    //   => b == vec_trans c
    // assert (b == vec_trans c);               // from spd_symmetric + constructor injectivity
    //   row: vec_scalar_mul (vec_trans l21) l11 == b
    //        vec_trans l21 = vec_scalar_div (vec_trans c) l11  [vec_trans_scalar_div]
    //        (vec_scalar_div (vec_trans c) l11) * l11 == vec_trans c == b  [vec_scalar_div_mul]
    // assert (vec_scalar_mul (vec_trans l21) l11 == b);  // MISSING: vec_scalar_div_mul (+ b == vec_trans c)
    //   top-left: mat_add (outer_prod l21 (vec_trans l21)) (mat_mul l (transpose l)) == d
    //     mat_mul l (transpose l) == s  (recursive)
    //     outer_prod l21 (vec_trans l21) == outer_prod (vec_scalar_div c a) b:
    //       outer_prod (c/l11) ((vec_trans c)/l11)          [vec_trans_scalar_div]
    //       = outer_prod ((c/l11)/l11) (vec_trans c)        [outer_prod_div_comm]
    //       = outer_prod (c/(l11*l11)) (vec_trans c)        [vec_scalar_div_assoc]
    //       = outer_prod (c/a) (vec_trans c)                [l11*l11==a, b==vec_trans c]
    // assert (outer_prod l21 (vec_trans l21) == outer_prod (vec_scalar_div c a) b);
    //     mat_add (outer_prod (vec_scalar_div c a) b) s == d  [s = mat_sub d (outer_prod lc b)]
    // assert (mat_add (outer_prod (vec_scalar_div c a) b) s == d);  // MISSING: mat_add_sub_cancel
    // assert (mat_mul l' (transpose l') == m);
    l'

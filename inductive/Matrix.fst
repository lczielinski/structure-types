module Matrix

open Scalar
open Vector
open MatrixType

(* matrix-vector mul *)
assume val mat_vec_mul (#n: pos) (m: mat n) (c1: cvec n)
    : c2: cvec n {(is_id m ==> c1 == c2) /\ (is_zero_vec c1 ==> is_zero_vec c2)}
// let rec mat_vec_mul (#n: pos) (m: mat n) (c: cvec n) = 
//   match m with 
//   | Mat1 a -> 
//     let Vec1 c1 = c in Vec1 #Col (scalar_mul a c1)
//   | MatN m' c a b -> magic()

assume val vec_mat_mul (#n: pos) (r1: rvec n) (m: mat n)
    : r2: rvec n {(is_id m ==> r1 == r2) /\ (is_zero_vec r1 ==> is_zero_vec r2)}

assume val mat_vec_mul_vec_neg (#n: pos) (m: mat n) (c: cvec n)
    : Lemma (mat_vec_mul m (vec_neg c) == vec_neg (mat_vec_mul m c))
      [SMTPat (mat_vec_mul m (vec_neg c))]

assume val mat_vec_mul_scalar (#n: pos) (m: mat n) (c: cvec n) (a: num)
    : Lemma (mat_vec_mul m (vec_scalar_mul c a) == vec_scalar_mul (mat_vec_mul m c) a)
      [SMTPat (mat_vec_mul m (vec_scalar_mul c a))]

(* outer product *)
assume val outer_prod (#n: pos) (c: cvec n) (r: rvec n)
    : m: mat n {(is_zero_vec c \/ is_zero_vec r) ==> is_zero_mat m}

assume val outer_prod_div_comm (#n: pos) (c: cvec n) (b: rvec n) (l: num{is_nnz l})
    : Lemma (outer_prod c (vec_scalar_div b l) == outer_prod (vec_scalar_div c l) b)
      [SMTPat (outer_prod c (vec_scalar_div b l))]

(* matrix addition *)
let rec mat_add (#n: pos) (m1 m2: mat n) : mat n =
  match m1 with
  | Mat1 a -> let Mat1 b = m2 in Mat1 (scalar_add a b)
  | MatN m1' col1 corner1 row1 ->
    let MatN m2' col2 corner2 row2 = m2 in
    MatN (mat_add m1' m2') (vec_add col1 col2) (scalar_add corner1 corner2) (vec_add row1 row2)

let rec mat_add_zero_l (#n: pos) (m1 m2: mat n)
    : Lemma (requires is_zero_mat m1) (ensures mat_add m1 m2 == m2) [SMTPat (mat_add m1 m2)] =
  match m1 with
  | Mat1 _ -> let Mat1 _ = m2 in ()
  | MatN m1' _ _ _ ->
    let MatN m2' _ _ _ = m2 in
    mat_add_zero_l m1' m2'

let rec mat_add_zero_r (#n: pos) (m1 m2: mat n)
    : Lemma (requires is_zero_mat m2) (ensures mat_add m1 m2 == m1) [SMTPat (mat_add m1 m2)] =
  match m1 with
  | Mat1 _ -> let Mat1 _ = m2 in ()
  | MatN m1' _ _ _ ->
    let MatN m2' _ _ _ = m2 in
    mat_add_zero_r m1' m2'

(* matrix negation *)
let rec mat_neg (#n: pos) (m: mat n) : mat n =
  match m with
  | Mat1 a -> Mat1 (scalar_neg a)
  | MatN m' c a b -> MatN (mat_neg m') (vec_neg c) (scalar_neg a) (vec_neg b)

(* matrix subtraction *)
let mat_sub (#n: pos) (m1 m2: mat n) : mat n = mat_add m1 (mat_neg m2)

assume val mat_add_sub_cancel (#n: pos) (m1 m2: mat n)
    : Lemma (mat_add m2 (mat_sub m1 m2) == m1)
      [SMTPat (mat_add m2 (mat_sub m1 m2))]

(* schur complement *)
// let schur1 (#n: pos{n >= 2}) (m: mat n{rowsdd m}) : mat n = 
//   match m with 
//   | MatN #n m' c a b -> 
//     assert (m' : mat n); 
//     mat_sub m' (outer_prod (vec_scalar_div c a) b)


let schur1 (#n: pos) (d: mat n) (c: cvec n) (a: num{is_nnz a}) (b: rvec n) : mat n =
  mat_sub d (outer_prod (vec_scalar_div c a) b)

assume val schur1_spd (#n: pos) (d: mat n) (c: cvec n) (a: num{is_nnz a}) (b: rvec n)
    : Lemma (requires spd (MatN d c a b)) (ensures spd (schur1 d c a b)) [SMTPat (schur1 d c a b)]

assume val schur1_rowsdd (#n: pos) (d: mat n) (c: cvec n) (a: num{is_nnz a}) (b: rvec n)
    : Lemma (requires rowsdd (MatN d c a b))
      (ensures rowsdd (schur1 d c a b))
      [SMTPat (schur1 d c a b)]

assume val schur1_inv (#n: pos) (d: mat n) (c: cvec n) (a: num{is_nnz a}) (b: rvec n)
    : Lemma (requires inv (MatN d c a b)) (ensures inv (schur1 d c a b)) [SMTPat (schur1 d c a b)]

(* transpose *)
let rec transpose (#n: pos) (m: mat n) : mat n =
  match m with
  | Mat1 a -> Mat1 a
  | MatN m' c a b -> MatN (transpose m') (vec_trans b) a (vec_trans c)

let rec transpose_involutive (#n: pos) (m: mat n)
    : Lemma (transpose (transpose m) == m) [SMTPat (transpose (transpose m))] =
  match m with
  | Mat1 _ -> ()
  | MatN m' _ _ _ -> transpose_involutive m'

(* symmetry *)
let symmetric (#n: pos) (m: mat n) : prop = m == transpose m

assume val one_by_one_sym : m:mat 1 -> Lemma (symmetric m) [SMTPat (symmetric m)]

// let matN_symmetric (#n: pos) (m: mat n) (col: cvec n) (corner: num) (row: rvec n)
//     : Lemma (requires symmetric (MatN m col corner row))
//       (ensures vec_trans col == row /\ vec_trans row == col)
//       [SMTPat (symmetric (MatN m col corner row))] = ()

assume val spd_symmetric (#n: pos) (m: mat n)
    : Lemma (requires spd m) (ensures symmetric m) [SMTPat (spd m)]
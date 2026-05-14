module Matrix

open Scalar
open Vector
open MatrixType

(* matrix-vector mul *)
let rec mat_vec_mul (#n: pos) (m: mat n) (c1: cvec n) : c2: cvec n 
  {(is_id m ==> c2 == c1) /\ (is_zero_vec c1 ==> is_zero_vec c2)} =
  match m with
  | Mat1 a ->
    let Vec1 x = c1 in Vec1 (scalar_mul a x)
  | MatN m' c a b ->
    let VecN c1' x = c1 in
    VecN (vec_add (mat_vec_mul m' c1') (vec_scalar_mul c x))
         (scalar_add (inner_prod b c1') (scalar_mul a x))

let rec mat_vec_mul_vec_neg (#n: pos) (m: mat n) (c: cvec n)
    : Lemma (mat_vec_mul m (vec_neg c) == vec_neg (mat_vec_mul m c))
      [SMTPat (mat_vec_mul m (vec_neg c))] =
  match m with
  | Mat1 _ -> let Vec1 _ = c in ()
  | MatN m' _ _ _ ->
    let VecN c' _ = c in
    mat_vec_mul_vec_neg m' c'

assume val mat_vec_mul_scalar (#n: pos) (m: mat n) (c: cvec n) (a: num)
    : Lemma (mat_vec_mul m (vec_scalar_mul c a) == vec_scalar_mul (mat_vec_mul m c) a)
      [SMTPat (mat_vec_mul m (vec_scalar_mul c a))]
  // match m with
  // | Mat1 a' ->
  //   let Vec1 x = c in
  //   scalar_mul_assoc a' x a
  // | MatN m' col a' _ ->
  //   let VecN c' x = c in
  //   mat_vec_mul_scalar m' c' a;
  //   scalar_mul_assoc a' x a

assume val mat_vec_mul_div_scalar (#n: pos) (m: mat n) (c: cvec n) (a: num{is_nnz a})
    : Lemma (vec_scalar_mul (mat_vec_mul m (vec_scalar_div c a)) a == mat_vec_mul m c)
      [SMTPat (vec_scalar_mul (mat_vec_mul m (vec_scalar_div c a)) a)]

(* row-vector times matrix *)
let rec vec_mat_mul (#n: pos) (r1: rvec n) (m: mat n) : r2: rvec n 
  {(is_id m ==> r2 == r1) /\ (is_zero_vec r1 ==> is_zero_vec r2)} =
  match m with
  | Mat1 a ->
    let Vec1 x = r1 in Vec1 (scalar_mul x a)
  | MatN m' c a b ->
    let VecN r1' x = r1 in
    VecN (vec_add (vec_mat_mul r1' m') (vec_scalar_mul b x))
         (scalar_add (inner_prod r1' c) (scalar_mul x a))

(* outer product *)
let rec outer_prod (#n: pos) (c: cvec n) (r: rvec n)
    : m: mat n {(is_zero_vec c \/ is_zero_vec r) ==> is_zero_mat m} =
  match c with
  | Vec1 x ->
    let Vec1 y = r in
    Mat1 (scalar_mul x y)
  | VecN c' x ->
    let VecN r' y = r in
    MatN (outer_prod c' r') (vec_scalar_mul c' y) (scalar_mul x y) (vec_scalar_mul r' x)

assume val outer_prod_div_comm (#n: pos) (c: cvec n) (b: rvec n) (l: num{is_nnz l})
    : Lemma (outer_prod c (vec_scalar_div b l) == outer_prod (vec_scalar_div c l) b)
      [SMTPat (outer_prod c (vec_scalar_div b l))]

(* matrix addition *)
let rec mat_add (#n: pos) (m1 m2: mat n) : m3: mat n 
  {(is_zero_mat m1 ==> m3 == m2) /\ (is_zero_mat m2 ==> m3 == m1)} =
  match m1 with
  | Mat1 a -> let Mat1 b = m2 in Mat1 (scalar_add a b)
  | MatN m1' col1 corner1 row1 ->
    let MatN m2' col2 corner2 row2 = m2 in
    MatN (mat_add m1' m2') (vec_add col1 col2) (scalar_add corner1 corner2) (vec_add row1 row2)

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
let schur1 (#n: pos{n >= 2}) (m: mat n{top_left_nnz m})
    : mat (n - 1) =
  let MatN d c a b = m in
  mat_sub d (outer_prod (vec_scalar_div c a) b)

assume val schur1_spd (#n: pos{n >= 2}) (m: mat n)
    : Lemma (requires spd m)
      (ensures spd (schur1 m))
      [SMTPat (schur1 m)]

assume val schur1_rowsdd (#n: pos{n >= 2}) (m: mat n)
    : Lemma (requires rowsdd m)
      (ensures rowsdd (schur1 m))
      [SMTPat (schur1 m)]

assume val schur1_inv (#n: pos{n >= 2}) (m: mat n)
    : Lemma (requires inv m /\ top_left_nnz m)
      (ensures inv (schur1 m))
      [SMTPat (schur1 m)]

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

assume val spd_symmetric (#n: pos) (m: mat n)
    : Lemma (requires spd m) (ensures symmetric m) [SMTPat (spd m)]

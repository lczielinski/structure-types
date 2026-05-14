module MatMul

open Scalar
open Vector
open MatrixType
open Matrix

let triangular_compat (#n: pos) (m1 m2: mat n) : prop =
  (lower m1 /\ lower m2) \/ (upper m1 /\ upper m2)

(* matrix-matrix multiplication via block formula *)
let rec mat_mul (#n: pos) (m1 m2: mat n) : r: mat n 
  {(lower m1 /\ lower m2 ==> lower r) /\
    (upper m1 /\ upper m2 ==> upper r) /\
    (triangular_compat m1 m2 /\ unit_diag m1 /\ unit_diag m2 ==> unit_diag r) /\
    (triangular_compat m1 m2 /\ pos_diag m1 /\ pos_diag m2 ==> pos_diag r) /\
    (triangular_compat m1 m2 /\ nnz_diag m1 /\ nnz_diag m2 ==> nnz_diag r) /\
    (is_id m1 ==> r == m2) /\ (is_id m2 ==> r == m1)} =
  match m1 with
  | Mat1 a -> let Mat1 b = m2 in Mat1 (scalar_mul a b)
  | MatN m1' c1 a1 b1 ->
    let MatN m2' c2 a2 b2 = m2 in
    MatN (mat_add (outer_prod c1 b2) (mat_mul m1' m2'))
      (vec_add (vec_scalar_mul c1 a2) (mat_vec_mul m1' c2))
      (scalar_add (scalar_mul a1 a2) (inner_prod b1 c2))
      (vec_add (vec_scalar_mul b2 a1) (vec_mat_mul b1 m2'))

(* mul associates with mat-vec mul *)
assume val mat_vec_mul_assoc (#n: pos) (m1 m2: mat n) (c: cvec n)
    : Lemma (mat_vec_mul (mat_mul m1 m2) c == mat_vec_mul m1 (mat_vec_mul m2 c))
      [SMTPat (mat_vec_mul m1 (mat_vec_mul m2 c)); SMTPat (mat_mul m1 m2)]

(* inverses *)
let is_inverse (#n: pos) (l r: mat n) : prop = mat_mul r l == id_mat /\ mat_mul l r == id_mat

assume val mat_mul_perm (#n: pos) (m1 m2: mat n)
    : Lemma (requires perm m1 /\ perm m2)
      (ensures perm (mat_mul m1 m2))
      [SMTPat (perm (mat_mul m1 m2))]

assume val mat_mul_assoc (#n: pos) (m1 m2 m3: mat n)
    : Lemma (mat_mul (mat_mul m1 m2) m3 == mat_mul m1 (mat_mul m2 m3))
      [SMTPat (mat_mul (mat_mul m1 (transpose m2)) m3)]

assume val mat_mul_sub_distr (#n: pos) (m m1 m2: mat n)
    : Lemma (mat_mul m (mat_sub m1 m2) == mat_sub (mat_mul m m1) (mat_mul m m2))
      [SMTPat (mat_mul m (mat_sub m1 m2))]

assume val mat_mul_outer_prod (#n: pos) (m: mat n) (c: cvec n) (r: rvec n)
    : Lemma (mat_mul m (outer_prod c r) == outer_prod (mat_vec_mul m c) r)
      [SMTPat (mat_mul m (outer_prod c r))]

assume val transpose_perm (#n: pos) (m: mat n)
    : Lemma (requires perm m)
      (ensures perm (transpose m) /\ is_inverse m (transpose m))

assume val perm_inv_l (#n: pos) (p: mat n) (m: mat n)
    : Lemma (requires perm p)
      (ensures mat_mul (transpose p) (mat_mul p m) == m)
      [SMTPat (mat_mul (transpose p) (mat_mul p m))]

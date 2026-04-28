module MatMul

open Scalar
open Vector
open MatrixType
open Matrix

(* matrix-matrix mul *)
let triangular_compat (#n:pos) (m1 m2:mat n) : prop =
  (lower m1 /\ lower m2) \/ (upper m1 /\ upper m2)

assume val mat_mul : #n:pos -> mat n -> mat n -> mat n

assume val mat_mul_lower : #n:pos -> m1:mat n -> m2:mat n ->
  Lemma (requires lower m1 /\ lower m2)
        (ensures lower (mat_mul m1 m2))
        [SMTPat (lower (mat_mul m1 m2))]

assume val mat_mul_upper : #n:pos -> m1:mat n -> m2:mat n ->
  Lemma (requires upper m1 /\ upper m2)
        (ensures upper (mat_mul m1 m2))
        [SMTPat (upper (mat_mul m1 m2))]

assume val mat_mul_unit_diag : #n:pos -> m1:mat n -> m2:mat n ->
  Lemma (requires triangular_compat m1 m2 /\ unit_diag m1 /\ unit_diag m2)
        (ensures unit_diag (mat_mul m1 m2))
        [SMTPat (unit_diag (mat_mul m1 m2))]

assume val mat_mul_pos_diag : #n:pos -> m1:mat n -> m2:mat n ->
  Lemma (requires triangular_compat m1 m2 /\ pos_diag m1 /\ pos_diag m2)
        (ensures pos_diag (mat_mul m1 m2))
        [SMTPat (pos_diag (mat_mul m1 m2))]

assume val mat_mul_nnz_diag : #n:pos -> m1:mat n -> m2:mat n ->
  Lemma (requires triangular_compat m1 m2 /\ nnz_diag m1 /\ nnz_diag m2)
        (ensures nnz_diag (mat_mul m1 m2))
        [SMTPat (nnz_diag (mat_mul m1 m2))]

assume val mat_mul_id_l : #n:pos -> m:mat n ->
  Lemma (mat_mul _id_mat m == m) [SMTPat (mat_mul _id_mat m)]

assume val mat_mul_id_r : #n:pos -> m:mat n ->
  Lemma (mat_mul m _id_mat == m) [SMTPat (mat_mul m _id_mat)]

(* mul associates *)
assume val mat_vec_mul_assoc : #n:pos -> m1:mat n -> m2:mat n -> c:cvec n ->
  Lemma (ensures mat_vec_mul (mat_mul m1 m2) c == mat_vec_mul m1 (mat_vec_mul m2 c))
        [SMTPat (mat_vec_mul m1 (mat_vec_mul m2 c)); SMTPat (mat_mul m1 m2)]

(* inverses *)
let is_inverse (#n:pos) (l r:mat n) : prop =
  (mat_mul r l == _id_mat) /\ (mat_mul l r == _id_mat)

assume val mul_augment : #n:pos{n >= 2} ->
  m1:mat (n-1) -> c1:cvec (n-1) -> a1:num -> b1:rvec (n-1) ->
  m2:mat (n-1) -> c2:cvec (n-1) -> a2:num -> b2:rvec (n-1) ->
  Lemma (ensures mat_mul #n (augment m1 c1 a1 b1) (augment m2 c2 a2 b2)
              == augment (mat_add (outer_prod c1 b2) (mat_mul m1 m2))
                         (vec_add (vec_scalar_mul c1 a2) (mat_vec_mul m1 c2))
                         (scalar_add (scalar_mul a1 a2) (inner_prod b1 c2))
                         (vec_add (vec_scalar_mul b2 a1) (vec_mat_mul b1 m2)))
        [SMTPat (mat_mul (augment m1 c1 a1 b1) (augment m2 c2 a2 b2))]
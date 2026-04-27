module Matrix

open Scalar
open Vector
open MatrixType

(* destructors *)
assume val destruct : #n:pos{n >= 2} -> m:mat(n) ->
  c:cvec(n-1) & a:num & b:rvec(n-1) & d:mat(n-1) {
    (lower m ==> lower d /\ zero_rvec b) /\
    (upper m ==> upper d /\ zero_cvec c) /\
    (unit_diag m ==> one a /\ unit_diag d) /\
    (pos_diag m ==> posr a /\ pos_diag d) /\
    (nnz_diag m ==> nnz a /\ nnz_diag d) /\
    (rowsdd m ==> rowsdd d) /\
    (spd m ==> spd d /\ posr a)
  }

(* augmenters *)
assume val augment : #n:pos{n >= 2} -> m:mat(n-1) -> 
  c:cvec(n-1) -> a:num -> b:rvec(n-1) -> d:mat(n) {
    (lower m /\ zero_rvec b ==> lower d) /\
    (upper m /\ zero_cvec c ==> upper d) /\
    (unit_diag m /\ one a ==> unit_diag d) /\
    (pos_diag m /\ posr a ==> pos_diag d) /\
    (nnz_diag m /\ nnz a ==> nnz_diag d) /\
    (spd m /\ posr a ==> spd d)
  }

(* augment id with zero vec *)
assume val augment_identity_zero : #m:pos -> #n:pos{n>= 2} ->
    Lemma (requires n = m + 1)
      (ensures augment #n _id_mat _zero_cvec _one _zero_rvec == _id_mat)
    [SMTPat (augment #n (_id_mat #m) (_zero_cvec #m) _one (_zero_rvec #m))]

(* destructing then augmenting recovers the original matrix *)
assume val augment_destruct_lower_inv : #n:pos{n >= 2} -> m:mat(n) ->
    Lemma (ensures (let (|c, a, b, d|) = destruct m in
                    augment d c a b == m))
    [SMTPat (destruct m)]

(* matrix-vector mul *)
assume val mat_vec_mul : #n:pos -> mat(n) -> cvec(n) -> cvec(n)

(* id mul with vec *)
assume val mat_vec_mul_identity : #n:pos -> c:cvec(n) ->
    Lemma (ensures mat_vec_mul _id_mat c == c)
    [SMTPat (mat_vec_mul _id_mat c)]

(* mul by neg vec *)
assume val mat_vec_mul_neg : #n:pos -> m:mat(n) -> c:cvec(n) ->
    Lemma (ensures mat_vec_mul m (neg c) == neg (mat_vec_mul m c))
    [SMTPat (mat_vec_mul m (neg c))]

(* matrix-matrix mul *)
let triangular_compat (#n:pos) (m1 m2:mat(n)) : prop =
    (lower m1 /\ lower m2) \/ (upper m1 /\ upper m2)
  
assume val mat_mul : #n:pos -> m1:mat(n) -> m2:mat(n) -> m3:mat(n) {
    (lower m1 /\ lower m2 ==> lower m3) /\
    (upper m1 /\ upper m2 ==> upper m3) /\
    (triangular_compat m1 m2 /\ unit_diag m1 /\ unit_diag m2 ==> unit_diag m3) /\
    (triangular_compat m1 m2 /\ pos_diag m1 /\ pos_diag m2 ==> pos_diag m3) /\
    (triangular_compat m1 m2 /\ nnz_diag m1 /\ nnz_diag m2 ==> nnz_diag m3) /\
    (identity m1 ==> m3 == m2) /\ (identity m2 ==> m3 == m1) 
}

(* mul associates *)
assume val mat_vec_mul_assoc : #n:pos -> m1:mat(n) -> m2:mat(n) -> c:cvec(n) ->
    Lemma (ensures mat_vec_mul (mat_mul m1 m2) c == mat_vec_mul m1 (mat_vec_mul m2 c))
    [SMTPatOr [
       [SMTPat (mat_vec_mul (mat_mul m1 m2) c)];
       [SMTPat (mat_vec_mul m1 (mat_vec_mul m2 c))]
    ]]

assume val mul_augment_lower : #m:pos -> #n:pos ->
  m1:mat(m){lower m1} -> c1:cvec(m) -> a1:num ->
  m2:mat(m){lower m2} -> c2:cvec(m) -> a2:num ->
  Lemma (requires n = m + 1)
      (ensures (mat_mul #n (augment m1 c1 a1 _zero_rvec) (augment m2 c2 a2 _zero_rvec) 
      == augment (mat_mul m1 m2) (cvec_add (mat_vec_mul m1 c2) (vec_scalar_mul c1 a2))
      (scalar_mul a1 a2) _zero_rvec))
    [SMTPat (mat_mul #n (augment m1 c1 a1 (_zero_rvec #m)) (augment m2 c2 a2 (_zero_rvec #m)))]

(* inverses *)
let is_inverse (#n:pos) (l r : mat(n)) : prop =
    (mat_mul r l == _id_mat) /\ (mat_mul l r == _id_mat)

(* 1x1 unit diag matrix is the identity *)
assume val one_by_one_is_identity : l:mat(1) ->
    Lemma (requires unit_diag l) (ensures l == _id_mat)
    [SMTPat (unit_diag l)]

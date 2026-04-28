module Matrix

open Scalar
open Vector
open MatrixType

(* destructors *)
assume val destruct : #n:pos{n >= 2} -> m:mat(n) ->
  c:cvec(n-1) & a:num & b:rvec(n-1) & d:mat(n-1) {
    (lower m ==> lower d /\ zero_vec b) /\
    (upper m ==> upper d /\ zero_vec c) /\
    (unit_diag m ==> one a /\ unit_diag d) /\
    (pos_diag m ==> posr a /\ pos_diag d) /\
    (nnz_diag m ==> nnz a /\ nnz_diag d) /\
    (rowsdd m ==> rowsdd d) /\
    (spd m ==> spd d /\ posr a)
  }

(* augmenters *)
assume val augment : #n:pos{n >= 2} -> m:mat(n-1) -> 
  c:cvec(n-1) -> a:num -> b:rvec(n-1) -> d:mat(n) {
    (lower m /\ zero_vec b ==> lower d) /\
    (upper m /\ zero_vec c ==> upper d) /\
    (unit_diag m /\ one a ==> unit_diag d) /\
    (pos_diag m /\ posr a ==> pos_diag d) /\
    (nnz_diag m /\ nnz a ==> nnz_diag d) /\
    (spd m /\ posr a ==> spd d)
  }

(* augment id with zero vec *)
assume val augment_identity_zero : #m:pos -> #n:pos{n >= 2} ->
    Lemma (requires n = m + 1)
    (ensures augment #n _id_mat _zero_cvec _one _zero_rvec == _id_mat)
    [SMTPat (augment #n (_id_mat #m) (_zero_cvec #m) _one (_zero_rvec #m))]

(* destructing then augmenting recovers the original matrix *)
assume val augment_destruct_lower_inv : #n:pos{n >= 2} -> m:mat(n) ->
    Lemma (ensures (let (|c, a, b, d|) = destruct m in
                    augment d c a b == m))
    [SMTPat (destruct m)]

(* matrix-vector mul *)
assume val mat_vec_mul : #n:pos -> m:mat(n) -> c1:cvec(n) -> c2:cvec(n) {
    (identity m ==> c1 == c2) /\
    (zero_vec c1 ==> zero_vec c2)
}

assume val vec_mat_mul : #n:pos -> r1:rvec(n) -> m:mat(n) -> r2:rvec(n) {
    (identity m ==> r1 == r2) /\ 
    (zero_vec r1 ==> zero_vec r2)
}

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

(* inverses *)
let is_inverse (#n:pos) (l r : mat(n)) : prop =
    (mat_mul r l == _id_mat) /\ (mat_mul l r == _id_mat)

(* 1x1 unit diag matrix is the identity *)
assume val one_by_one_is_identity : l:mat(1) ->
    Lemma (requires unit_diag l) (ensures l == _id_mat)
    [SMTPat (unit_diag l)]

(* outer product *)
assume val outer_prod : #n:pos -> c:cvec(n) -> r:rvec(n) -> m:mat(n){
    (zero_vec c \/ zero_vec r) ==> zero_mat m
}

(* adding matrices *)
assume val mat_add : #n:pos -> m1:mat(n) -> m2:mat(n) -> m3:mat(n){
    (zero_mat m1 ==> m2 == m3) /\ (zero_mat m2 ==> m1 == m3)
}
assume val mat_sub : #n:pos -> mat(n) -> mat(n) -> mat(n)

assume val mat_add_sub : #n:pos -> m1:mat(n) -> m2:mat(n) ->
    Lemma (ensures mat_add m1 (mat_sub m2 m1) == m2)
    [SMTPat (mat_add m1 (mat_sub m2 m1))]

assume val mul_augment : #n:pos{n >= 2} ->
  m1:mat(n-1) -> c1:cvec(n-1) -> a1:num -> b1:rvec(n-1) ->
  m2:mat(n-1) -> c2:cvec(n-1) -> a2:num -> b2:rvec(n-1) ->
  Lemma (ensures (mat_mul #n (augment m1 c1 a1 b1) (augment m2 c2 a2 b2))
    == augment (mat_add (outer_prod c1 b2) (mat_mul m1 m2))
        (vec_add (vec_scalar_mul c1 a2) (mat_vec_mul m1 c2))
        (scalar_add (scalar_mul a1 a2) (inner_prod b1 c2))
        (vec_add (vec_scalar_mul b2 a1) (vec_mat_mul b1 m2)))
  [SMTPat (mat_mul (augment m1 c1 a1 b1) (augment m2 c2 a2 b2))]

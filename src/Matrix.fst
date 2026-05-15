module Matrix

open Scalar
open Vector
open MatrixType

(* destructors *)
assume val destruct_rowsdd (#n: pos{n >= 2}) (m: mat n)
    : Lemma (requires rowsdd m) (ensures (let MatN m' c a b = m in rowsdd m')) [SMTPat (rowsdd m)]
assume val destruct_spd (#n: pos{n >= 2}) (m: mat n)
    : Lemma (requires spd m) (ensures (let MatN m' c a b = m in spd m' /\ is_pos a)) [SMTPat (spd m)]

assume val augment_perm (#n: pos) (m: mat n) :
  Lemma (requires perm m) (ensures perm (MatN m zero_cvec one zero_rvec)) [SMTPat (perm m)]

(* matrix-vector mul *)
assume val mat_vec_mul : #n:pos -> m:mat n -> c1:cvec n -> c2:cvec n{
  (identity m ==> c1 == c2) /\ (is_zero_vec c1 ==> is_zero_vec c2)
}

assume val vec_mat_mul : #n:pos -> r1:rvec n -> m:mat n -> r2:rvec n{
  (identity m ==> r1 == r2) /\ (is_zero_vec r1 ==> is_zero_vec r2)
}

(* mul by neg vec *)
assume val mat_vec_mul_neg : #n:pos -> m:mat n -> c:cvec n ->
  Lemma (mat_vec_mul m (neg c) == neg (mat_vec_mul m c))
        [SMTPat (mat_vec_mul m (neg c))]

(* m * (a * c) == a * (m * c) *)
assume val mat_vec_mul_scalar : #n:pos -> m:mat n -> c:cvec n -> a:num ->
  Lemma (mat_vec_mul m (vec_scalar_mul c a) == vec_scalar_mul (mat_vec_mul m c) a)
  [SMTPat (mat_vec_mul m (vec_scalar_mul c a))]

(* outer product *)
assume val outer_prod : #n:pos -> c:cvec n -> r:rvec n -> m:mat n{
  (is_zero_vec c \/ is_zero_vec r) ==> zero_mat m
}

(* outer prod of scalar div *)
assume val outer_prod_div_comm : #n:pos -> c:cvec n -> b:rvec n -> l:num{is_nnz l} ->
  Lemma (outer_prod c (vec_scalar_div b l) == outer_prod (vec_scalar_div c l) b)
  [SMTPat (outer_prod c (vec_scalar_div b l))]

(* adding matrices *)
assume val mat_add : #n:pos -> m1:mat n -> m2:mat n -> m3:mat n{
  (zero_mat m1 ==> m2 == m3) /\ (zero_mat m2 ==> m1 == m3)
}

assume val mat_sub : #n:pos -> m1:mat n -> m2:mat n -> m3:mat n{
  mat_add m2 m3 == m1
}

(* schur complement *)
assume val schur1 : #n:pos -> d:mat n -> c:cvec n -> a:num{is_nnz a} -> b:rvec n ->
  s:mat n{
    s == mat_sub d (outer_prod (vec_scalar_div c a) b) /\
    (spd    (MatN d c a b) ==> spd    s) /\
    (rowsdd (MatN d c a b) ==> rowsdd s) /\
    (inv    (MatN d c a b) ==> inv    s)
  }

(* transpose *)
assume val transpose : #n:pos -> mat n -> mat n

assume val transpose_involutive : #n:pos -> m:mat n ->
  Lemma (transpose (transpose m) == m) [SMTPat (transpose (transpose m))]

assume val transpose_augment : #n:pos -> #k:pos{k == n + 1} ->
  m:mat n -> c:cvec n -> a:num -> b:rvec n ->
  Lemma (ensures (transpose #k (MatN m c a b)
                  == MatN #n (transpose m) (trans_vec b) a (trans_vec c)))
        [SMTPat (transpose #k (MatN m c a b))]

(* symmetry *)
let symmetric (#n:pos) (m:mat n) : prop = m == transpose m

assume val destruct_symmetric : #n:pos{n >= 2} -> m:mat n ->
  Lemma (requires symmetric m)
        (ensures (let (MatN d c a b) = m in
                  trans_vec c == b /\ trans_vec b == c))
        [SMTPat (symmetric m)]

assume val spd_symmetric : #n:pos -> m:mat n ->
  Lemma (requires spd m) (ensures symmetric m) [SMTPat (spd m)]

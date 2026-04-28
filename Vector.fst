module Vector

open Scalar

assume type vec : pos -> Type

assume val row : #n:pos -> vec n -> prop
let col (#n:pos) (v:vec n) : prop = ~(row v)

let rvec (n:pos) = r:vec n{row r}
let cvec (n:pos) = c:vec n{col c}

let vec_compat (#n:pos) (v1 v2:vec n) : prop =
  (col v1 /\ col v2) \/ (row v1 /\ row v2)

(* zero vector *)
assume val _zero_cvec : #n:pos -> cvec n
assume val _zero_rvec : #n:pos -> rvec n

let zero_vec (#n:pos) (v:vec n) : prop =
  (row v /\ v == _zero_rvec #n) \/ (col v /\ v == _zero_cvec #n)

(* add vectors *)
assume val vec_add : #n:pos -> v1:vec n -> v2:vec n{vec_compat v1 v2} -> v3:vec n{
  (zero_vec v1 ==> v3 == v2) /\
  (zero_vec v2 ==> v3 == v1) /\
  (col v1 ==> col v3) /\
  (row v1 ==> row v3)
}

(* negate a vector *)
assume val neg : #n:pos -> v1:vec n -> v2:vec n{
  (col v1 ==> col v2) /\ (row v1 ==> row v2)
}

assume val neg_zero : #n:pos -> v:vec n ->
  Lemma (requires zero_vec v) (ensures zero_vec (neg v)) [SMTPat (neg v)]

assume val neg_add_inv_l : #n:pos -> v:vec n ->
  Lemma (zero_vec (vec_add v (neg v))) [SMTPat (vec_add v (neg v))]

assume val neg_add_inv_r : #n:pos -> v:vec n ->
  Lemma (zero_vec (vec_add (neg v) v)) [SMTPat (vec_add (neg v) v)]

assume val neg_involutive : #n:pos -> v:vec n ->
  Lemma (neg (neg v) == v) [SMTPat (neg (neg v))]

(* vector-scalar mult *)
assume val vec_scalar_mul : #n:pos -> v1:vec n -> a:num -> v2:vec n{
  (col v1 ==> col v2) /\
  (row v1 ==> row v2)
}

assume val vec_scalar_mul_zero : #n:pos -> v:vec n -> a:num ->
  Lemma (requires zero_vec v) (ensures zero_vec (vec_scalar_mul v a)) 
  [SMTPat (vec_scalar_mul v a)]

assume val vec_scalar_mul_one : #n:pos -> v:vec n -> a:num ->
  Lemma (requires one a) (ensures vec_scalar_mul v a == v) 
  [SMTPat (vec_scalar_mul v a)]

assume val vec_scalar_div : #n:pos -> v1:vec n -> a:num{nnz a} -> v2:vec n{
  (col v1 ==> col v2) /\ (row v1 ==> row v2) /\
  vec_scalar_mul v2 a == v1
}

(* inner product *)
assume val inner_prod : #n:pos -> rvec n -> cvec n -> num

assume val inner_prod_zero : #n:pos -> r:rvec n -> c:cvec n ->
  Lemma (requires zero_vec r \/ zero_vec c) (ensures zero (inner_prod r c)) 
  [SMTPat (inner_prod r c)]
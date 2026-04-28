module Vector

open Scalar

assume type vec : pos -> Type

(* row or column vectors *)
assume val row : #n:pos -> vec n -> prop
let col (#n:pos) (v:vec n) : prop = ~(row v)

let rvec (n:pos) = r:vec(n){row r}
let cvec (n:pos) = c:vec(n){col c}

(* zero vector *)
assume val zero_vec : #n:pos -> vec(n) -> prop

assume val _zero_cvec : #n:pos -> c:cvec(n){zero_vec c}
assume val _zero_rvec : #n:pos -> r:rvec(n){zero_vec r}

assume val zero_cvec_unique : #n:pos -> c:cvec(n) ->
    Lemma (requires zero_vec c) (ensures c == _zero_cvec #n)
    [SMTPat (zero_vec c)]

assume val zero_rvec_unique : #n:pos -> r:rvec(n) ->
    Lemma (requires zero_vec r) (ensures r == _zero_rvec #n)
    [SMTPat (zero_vec r)]

(* two vectors have same orientation *)
let vec_compat (#n:pos) (v1 v2:vec(n)) : prop =
    (col v1 /\ col v2) \/ (row v1 /\ row v2)

(* adding vectors *)
assume val vec_add : #n:pos -> v1:vec(n) -> 
    v2:vec(n){vec_compat v1 v2} -> v3:vec(n) {
    (zero_vec v1 ==> v3 == v2) /\ 
    (zero_vec v2 ==> v3 == v1) /\
    (col v1 ==> col v3) /\
    (row v1 ==> row v3)
  }

(* negate a vector *)
assume val neg : #n:pos -> v1:vec(n) -> v2:vec(n) {
    (col v1 ==> col v2) /\
    (row v1 ==> row v2) /\
    (zero_vec v1 ==> zero_vec v2)
}

assume val neg_involutive : #n:pos -> v:vec(n) ->
    Lemma (neg (neg v) == v) [SMTPat (neg (neg v))]

assume val vec_add_neg_r : #n:pos -> v:vec(n) ->
    Lemma (zero_vec (vec_add v (neg v)))
    [SMTPat (vec_add v (neg v))]

assume val vec_add_neg_l : #n:pos -> v:vec(n) ->
    Lemma (zero_vec (vec_add (neg v) v))
    [SMTPat (vec_add (neg v) v)]

(* vector-scalar mul *)
assume val vec_scalar_mul : #n:pos -> v1:vec(n) -> a:num -> v2:vec(n) {
    (col v1 ==> col v2) /\ (row v1 ==> row v2) /\
    (zero_vec v1 ==> zero_vec v2) /\
    (one a ==> v1 == v2)
}

(* vector-scalar div *)
assume val vec_scalar_div : #n:pos -> v1:vec n -> a:num{nnz a} -> v2:vec n {
    (col v1 ==> col v2) /\ (row v1 ==> row v2) /\
    (vec_scalar_mul v2 a == v1)
}

(* inner product *)
assume val inner_prod : #n:pos -> r:rvec(n) -> c:cvec(n) -> a:num {
    zero_vec r \/ zero_vec c ==> zero a
}

assume val zero_vec_zero_cvec : #n:pos ->
  Lemma (zero_vec (_zero_cvec #n))
  [SMTPat (zero_vec (_zero_cvec #n))]

assume val zero_vec_zero_rvec : #n:pos ->
  Lemma (zero_vec (_zero_rvec #n))
  [SMTPat (zero_vec (_zero_rvec #n))]

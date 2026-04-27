module Vector

open Scalar

assume type cvec : pos -> Type
assume type rvec : pos -> Type

(* zero vector *)
assume val zero_cvec : #n:pos -> cvec(n) -> prop
assume val zero_rvec : #n:pos -> rvec(n) -> prop

assume val _zero_cvec : #n:pos -> c:cvec(n){zero_cvec c}
assume val _zero_rvec : #n:pos -> r:rvec(n){zero_rvec r}

assume val zero_cvec_unique : #n:pos -> c:cvec(n) ->
    Lemma (requires zero_cvec c) (ensures c == _zero_cvec #n)
    [SMTPat (zero_cvec c)]

assume val zero_rvec_unique : #n:pos -> r:rvec(n) ->
    Lemma (requires zero_rvec r) (ensures r == _zero_rvec #n)
    [SMTPat (zero_rvec r)]

(* adding vectors *)
assume val cvec_add : #n:pos -> c1:cvec(n) -> c2:cvec(n) -> c3:cvec(n) {
    (zero_cvec c1 ==> c3 == c2) /\ (zero_cvec c2 ==> c3 == c1)
}

(* negate a vector *)
assume val neg : #n:pos -> cvec(n) -> cvec(n)

assume val neg_involutive : #n:pos -> c:cvec(n) ->
    Lemma (neg (neg c) == c) [SMTPat (neg (neg c))]

assume val neg_zero : #n:pos -> c:cvec(n) ->
    Lemma (requires zero_cvec c) (ensures zero_cvec (neg c))
    [SMTPat (neg c)]

assume val cvec_add_neg_r : #n:pos -> c:cvec(n) ->
    Lemma (zero_cvec (cvec_add c (neg c)))
    [SMTPat (cvec_add c (neg c))]

assume val cvec_add_neg_l : #n:pos -> c:cvec(n) ->
    Lemma (zero_cvec (cvec_add (neg c) c))
    [SMTPat (cvec_add (neg c) c)]

(* vector-scalar mul *)
assume val vec_scalar_mul : #n:pos -> cvec(n) -> num -> cvec(n)

assume val vec_scalar_mul_one : #n:pos -> c:cvec(n) -> a:num ->
    Lemma (requires one a) (ensures vec_scalar_mul c a == c)
    [SMTPat (vec_scalar_mul c a)]

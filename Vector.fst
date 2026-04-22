module Vector

assume type cvec : pos -> Type

(* negate a vector*)
assume val neg : #n:pos -> cvec n -> cvec n

assume val vec_add : #n:pos -> cvec n -> cvec n -> cvec n

assume val zero_cvec : n:pos -> cvec n

assume val vec_add_neg : #n:pos -> v:cvec n ->
    Lemma (ensures vec_add v (neg v) == zero_cvec n /\
                   vec_add (neg v) v == zero_cvec n)
    [SMTPatOr [[SMTPat (vec_add v (neg v))]; 
               [SMTPat (vec_add (neg v) v)]]]

(* Zero is a unit for vec_add *)
assume val vec_add_zero : #n:pos -> v:cvec n ->
    Lemma (ensures vec_add v (zero_cvec n) == v /\
                   vec_add (zero_cvec n) v == v)
    [SMTPat (vec_add v (zero_cvec n)); SMTPat (vec_add (zero_cvec n) v)]

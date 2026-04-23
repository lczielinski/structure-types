module Matrix

open Scalar
open Vector
open MatrixType

(* destructors *)
assume val destruct_lower : #k:diag_kind -> #n:pos{n>=2} -> 
    lower_of k n -> cvec(n-1) & witness k & lower_of k (n-1)

(* augmenters *)
assume val augment_lower : #k:diag_kind -> #n:pos{n>=2} -> 
    lower_of k (n-1) -> cvec(n-1) -> witness k -> lower_of k (n)

(* destructing then augmenting recovers the original matrix *)
assume val augment_destruct_lower_inv : #k:diag_kind -> #n:pos{n>=2} -> 
    l:lower_of k (n) ->
    Lemma (ensures (let c, a, l' = destruct_lower l in
                    augment_lower l' c a == l))
    [SMTPat (destruct_lower l)]

(* matrix-vector mul *)
assume val mat_vec_mul : #n:pos -> mat(n) -> cvec(n) -> cvec(n)

(* mul by neg vec *)
assume val mat_vec_mul_neg : #n:pos -> m:mat(n) -> v:cvec n ->
    Lemma (ensures mat_vec_mul m (neg v) == neg (mat_vec_mul m v))
    [SMTPat (mat_vec_mul m (neg v))]

(* matrix-matrix mul *)
assume val mul_lower : #k:diag_kind -> #n:pos -> lower_of k (n) -> 
    lower_of k (n) -> lower_of k (n)

(* mul associates *)
assume val mat_vec_mul_assoc : #k:diag_kind -> #n:pos ->
    m1:lower_of k (n) -> m2:lower_of k (n) -> v:cvec n ->
    Lemma (ensures mat_vec_mul (mul_lower m1 m2) v == mat_vec_mul m1 (mat_vec_mul m2 v))
    [SMTPatOr [
       [SMTPat (mat_vec_mul (mul_lower m1 m2) v)];
       [SMTPat (mat_vec_mul m1 (mat_vec_mul m2 v))]
    ]]

(* multiplying augmented matrices *)
assume val mul_augment_lower : #k:diag_kind -> #n:pos{n >= 2} ->
    l:lower_of k (n-1) -> u:cvec(n-1) -> a:witness k ->
    r:lower_of k (n-1) -> v:cvec(n-1) -> b:witness k ->
    Lemma (ensures mul_lower (augment_lower l u a) (augment_lower r v b)
        == augment_lower (mul_lower l r)
                         (vec_add (vec_scalar_mul u b) (mat_vec_mul l v))
                         (scalar_mul a b))
    // [SMTPat (augment_lower l u a); SMTPat (augment_lower r v b)]
module Matrix

open Scalar
open Vector
open MatrixType

(* destructors *)
assume val destruct_lower : #k:num_kind -> #n:pos{n >= 2} ->
    lower_of k (n) -> cvec (n-1) & num_of k & lower_of k (n-1)

(* augmenters *)
assume val augment_lower : #k:num_kind -> #n:pos{n >= 2} ->
    lower_of k (n-1) -> cvec (n-1) -> num_of k -> lower_of k (n)

(* destructing then augmenting recovers the original matrix *)
assume val augment_destruct_lower_inv : #k:num_kind -> 
    #n:pos{n >= 2} -> l:lower_of k n ->
    Lemma (ensures (let c, a, l' = destruct_lower #k #n l in
                    augment_lower #k #n l' c a == l))
    [SMTPat (destruct_lower #k #n l)]

(* matrix-vector mul *)
assume val mat_vec_mul : #k:num_kind -> #n:pos -> lower_of k (n) -> cvec(n) -> cvec(n)

(* mul by neg vec *)
assume val mat_vec_mul_neg : #k:num_kind -> #n:pos -> m:lower_of k (n) -> v:cvec n ->
    Lemma (ensures mat_vec_mul #k #n m (neg v) == neg (mat_vec_mul #k #n m v))
    [SMTPat (mat_vec_mul #k #n m (neg v))]

(* matrix-matrix mul *)
assume val mul_lower : #k:num_kind -> #n:pos ->
    lower_of k (n) -> lower_of k (n) -> lower_of k (n)

(* mul associates *)
assume val mat_vec_mul_assoc : #k:num_kind -> #n:pos ->
    m1:lower_of k (n) -> m2:lower_of k (n) -> v:cvec(n) ->
    Lemma (ensures mat_vec_mul (mul_lower m1 m2) v == mat_vec_mul m1 (mat_vec_mul m2 v))
    [SMTPatOr [
       [SMTPat (mat_vec_mul #k #n (mul_lower #k #n m1 m2) v)];
       [SMTPat (mat_vec_mul #k #n m1 (mat_vec_mul #k #n m2 v))]
    ]]

(* multiplying augmented matrices *)
assume val mul_augment_lower : #k:num_kind -> #n:pos{n >= 2} ->
    l:lower_of k (n-1) -> u:cvec (n-1) -> a:num_of k ->
    r:lower_of k (n-1) -> v:cvec (n-1) -> b:num_of k ->
    Lemma (ensures mul_lower #k #n (augment_lower #k #n l u a) (augment_lower #k #n r v b)
        == augment_lower #k #n (mul_lower #k #(n-1) l r)
            (vec_add #(n-1) (vec_scalar_mul #(n-1) u b) (mat_vec_mul #k #(n-1) l v)) (scalar_mul a b))
    [SMTPat (mul_lower #k #n (augment_lower #k #n l u a) (augment_lower #k #n r v b))]

module Matrix

open Vector
open MatrixType

(* destructors *)
assume val destruct_lower_unitdiag : #n:pos{n >= 2} -> unit_lower n ->
    cvec (n - 1) & unit_lower (n - 1)

(* augmenters *)
assume val augment_lower_unitdiag : #n:pos{n >= 2} -> 
    unit_lower (n - 1) -> cvec (n - 1) -> unit_lower n

(* destructing then augmenting recovers the original matrix *)
assume val augment_destruct_inv : #n:pos{n >= 2} -> l:unit_lower n ->
    Lemma (ensures (let c, l' = destruct_lower_unitdiag l in
                    augment_lower_unitdiag l' c == l))
    [SMTPat (destruct_lower_unitdiag l)]

(* matrix-vector mul *)
assume val mat_vec_mul : #n:pos -> unit_lower n ->
    cvec n -> cvec n

(* mul by neg vec *)
assume val mat_vec_mul_neg : #n:pos ->
    m:unit_lower n -> v:cvec n ->
    Lemma (ensures mat_vec_mul m (neg v) == neg (mat_vec_mul m v))
    [SMTPat (mat_vec_mul m (neg v))]

(* matrix-matrix mul *)
assume val mat_mul : #n:pos -> unit_lower n ->
    unit_lower n -> unit_lower n

(* mul associates *)
assume val mat_vec_mul_assoc : #n:pos ->
    m1:unit_lower n -> m2:unit_lower n -> v:cvec n ->
    Lemma (ensures mat_vec_mul (mat_mul m1 m2) v == mat_vec_mul m1 (mat_vec_mul m2 v))
    [SMTPatOr [
       [SMTPat (mat_vec_mul (mat_mul m1 m2) v)];
       [SMTPat (mat_vec_mul m1 (mat_vec_mul m2 v))]
    ]]

(* multiplying augmented matrices *)
assume val mat_mul_augment : #n:pos{n >= 2} ->
    a:unit_lower (n-1) -> u:cvec (n-1) ->
    b:unit_lower (n-1) -> v:cvec (n-1) ->
    Lemma (ensures mat_mul (augment_lower_unitdiag a u) (augment_lower_unitdiag b v)
                == augment_lower_unitdiag (mat_mul a b) (vec_add (mat_vec_mul a v) u))
    [SMTPat (augment_lower_unitdiag #n a u); SMTPat (augment_lower_unitdiag #n b v)]

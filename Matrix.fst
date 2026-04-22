module Matrix

open Vector

type shape = | Lower
type diagonal = | UnitDiag

assume type sq_mat : pos -> shape -> diagonal -> Type

// {m : sq_mat n | lower(M) /\ unit(n) }

(* augmenters *)
assume val destruct_lower_unitdiag : #n:pos{n >= 2} -> sq_mat n Lower UnitDiag ->
    cvec (n - 1) * sq_mat (n - 1) Lower UnitDiag

assume val augment_lower_unitdiag : #n:pos{n >= 2} -> 
    sq_mat (n - 1) Lower UnitDiag -> cvec (n - 1) -> sq_mat n Lower UnitDiag

(* destructing then augmenting recovers the original matrix *)
assume val augment_destruct_inv : #n:pos{n >= 2} -> l:sq_mat n Lower UnitDiag ->
    Lemma (ensures (let c, l' = destruct_lower_unitdiag l in
                    augment_lower_unitdiag l' c == l))
    [SMTPat (destruct_lower_unitdiag l)]

(* matrix-vector mul *)
assume val mat_vec_mul : #n:pos -> sq_mat n Lower UnitDiag ->
    cvec n -> cvec n

(* mul by neg vec *)
assume val mat_vec_mul_neg : #n:pos ->
    m:sq_mat n Lower UnitDiag -> v:cvec n ->
    Lemma (ensures mat_vec_mul m (neg v) == neg (mat_vec_mul m v))
    [SMTPat (mat_vec_mul m (neg v))]

(* matrix-matrix mul *)
assume val mat_mul : #n:pos -> sq_mat n Lower UnitDiag ->
    sq_mat n Lower UnitDiag -> sq_mat n Lower UnitDiag

(* mul associates *)
assume val mat_vec_mul_assoc : #n:pos ->
    m1:sq_mat n Lower UnitDiag -> m2:sq_mat n Lower UnitDiag -> v:cvec n ->
    Lemma (ensures mat_vec_mul (mat_mul m1 m2) v == mat_vec_mul m1 (mat_vec_mul m2 v))
    [SMTPatOr [
       [SMTPat (mat_vec_mul (mat_mul m1 m2) v)];
       [SMTPat (mat_vec_mul m1 (mat_vec_mul m2 v))]
    ]]

(* multiplying augmented matrices *)
assume val mat_mul_augment : #n:pos{n >= 2} ->
    a:sq_mat (n-1) Lower UnitDiag -> u:cvec (n-1) ->
    b:sq_mat (n-1) Lower UnitDiag -> v:cvec (n-1) ->
    Lemma (ensures mat_mul (augment_lower_unitdiag a u) (augment_lower_unitdiag b v)
                == augment_lower_unitdiag (mat_mul a b) (vec_add (mat_vec_mul a v) u))
    [SMTPat (augment_lower_unitdiag #n a u); 
     SMTPat (augment_lower_unitdiag #n b v)]

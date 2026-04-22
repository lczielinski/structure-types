module Identity

open Vector
open Matrix

assume val identity : #n:pos -> unit_lower n

(* inverses *)
let is_inverse (#n:pos) (l r : unit_lower n) : prop =
    mat_mul r l == identity /\ mat_mul l r == identity

(* 1x1 unit diag matrix is the identity *)
assume val one_by_one_is_identity (l: unit_lower 1) :
    Lemma (ensures l == identity)
    [SMTPat (is_inverse l l)]

(* mul by id *)
assume val mul_identity_r (#n:pos) (m:unit_lower n) :
    Lemma (ensures mat_mul m identity == m)
    [SMTPat (mat_mul m identity)]

assume val mul_identity_l (#n:pos) (m:unit_lower n) :
    Lemma (ensures mat_mul identity m == m)
    [SMTPat (mat_mul identity m)]

(* augment id with zero vec *)
assume val augment_identity_zero : #n:pos{n >= 2} -> 
    Lemma (ensures augment_lower_unitdiag identity zero_cvec 
        == identity #n)
    [SMTPat (augment_lower_unitdiag #n identity zero_cvec)]

(* id mul with vec *)
assume val mat_vec_mul_identity : #n:pos -> v:cvec n ->
    Lemma (ensures mat_vec_mul identity v == v)
    [SMTPat (mat_vec_mul identity v)]

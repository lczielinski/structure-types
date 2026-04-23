module Identity

open Vector
open Matrix
open MatrixType

assume val identity : #n:pos -> lower_of unit_kind n

(* inverses *)
let is_inverse (#k:diag_kind) (#n:pos) (l r : lower_of k n) : prop =
    mul_lower r l == identity /\ mul_lower l r == identity

(* 1x1 unit diag matrix is the identity *)
assume val one_by_one_is_identity (l: unit_lower 1) :
    Lemma (ensures l == identity)
    [SMTPat (is_inverse l l)]

(* mul by id *)
assume val mul_identity_r (#n:pos) (m:unit_lower n) :
    Lemma (ensures mul_unit_lower m identity == m)
    [SMTPat (mul_unit_lower m identity)]

assume val mul_identity_l (#n:pos) (m:unit_lower n) :
    Lemma (ensures mul_unit_lower identity m == m)
    [SMTPat (mul_unit_lower identity m)]

(* augment id with zero vec *)
assume val augment_identity_zero : #n:pos{n >= 2} -> 
    Lemma (ensures augment_unit_lower identity zero_cvec 
        == identity #n)
    [SMTPat (augment_unit_lower #n identity zero_cvec)]

(* id mul with vec *)
assume val mat_vec_mul_identity : #n:pos -> v:cvec n ->
    Lemma (ensures mat_vec_mul identity v == v)
    [SMTPat (mat_vec_mul identity v)]

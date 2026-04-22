module Identity

open Vector
open Matrix

assume val identity : #n:pos -> sq_mat n Lower UnitDiag

(* inverses *)
unfold let is_inverse (#n:pos) (l r : sq_mat n Lower UnitDiag) : Type0 =
    mat_mul r l == identity /\ mat_mul l r == identity

(* 1x1 unit diag matrix is the identity *)
assume val one_by_one_is_identity (l:sq_mat 1 Lower UnitDiag) :
    Lemma (ensures l == identity)

(* mul by id *)
assume val mul_identity_r (#n:pos) (m:sq_mat n Lower UnitDiag) :
    Lemma (ensures mat_mul m identity == m)
    [SMTPat (mat_mul m identity)]

assume val mul_identity_l (#n:pos) (m:sq_mat n Lower UnitDiag) :
    Lemma (ensures mat_mul identity m == m)
    [SMTPat (mat_mul identity m)]

(* augment id with zero vec *)
assume val augment_identity_zero : #n:pos ->
    Lemma (ensures augment_lower_unitdiag (identity #n) (zero_cvec n) 
        == identity #(n + 1))
    [SMTPat (augment_lower_unitdiag (identity #n) (zero_cvec n))]

(* id mul with vec *)
assume val mat_vec_mul_identity : #n:pos -> v:cvec n ->
    Lemma (ensures mat_vec_mul identity v == v)
    [SMTPat (mat_vec_mul identity v)]

module Identity

open Scalar
open Vector
open Matrix
open MatrixType

assume val identity : #n:pos -> unit_lower(n)

(* inverses *)
let is_inverse (#k:num_kind) (#n:pos) (l r : lower_of k n) : prop =
    mul_lower #k #n r l == identity /\ mul_lower #k #n l r == identity

(* 1x1 unit diag matrix is the identity *)
assume val one_by_one_is_identity : l:unit_lower(1) ->
    Lemma (ensures l == identity)
    [SMTPat (is_inverse l l)]

(* mul by id *)
assume val mul_identity_r : #k:num_kind -> #n:pos -> m:lower_of k (n) ->
    Lemma (ensures mul_lower m identity == m)
    [SMTPat (mul_lower m identity)]

assume val mul_identity_l : #k:num_kind -> #n:pos -> m:lower_of k (n) ->
    Lemma (ensures mul_lower #k identity m == m)
    [SMTPat (mul_lower #k identity m)]

(* augment id with zero vec *)
assume val augment_identity_zero : #m:pos -> #n:pos -> o:one ->
    Lemma (requires n = m + 1)
          (ensures augment_lower #One #n identity zero_cvec o == identity)
    [SMTPat (augment_lower #One #n (identity #m) (zero_cvec #m) o)]

(* id mul with vec *)
assume val mat_vec_mul_identity : #n:pos -> v:cvec n ->
    Lemma (ensures mat_vec_mul identity v == v)
    [SMTPat (mat_vec_mul identity v)]
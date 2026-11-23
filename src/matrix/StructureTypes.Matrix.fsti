module StructureTypes.Matrix

open StructureTypes.Scalar
open StructureTypes.Vector

(* MCons a b c m is the block matrix [[a, b], [c, m]] *)
noeq type mat : nat -> Type =
  | MNil : mat 0
  | MCons : #n: nat -> num -> rvec n -> cvec n -> mat n -> mat (n + 1)

let rec mat_id (#n: nat) : mat n =
  if n = 0 then MNil else MCons scalar_one vec_zero vec_zero (mat_id #(n - 1))

let mat_is_id (#n: nat) (m: mat n) : prop = m == mat_id

let rec mat_zero (#n: nat) : mat n =
  if n = 0 then MNil else MCons scalar_zero vec_zero vec_zero (mat_zero #(n - 1))

let mat_is_zero (#n: nat) (m: mat n) : prop = m == mat_zero

let top_left_nnz (#n: nat) (m: mat n) : prop =
  match m with
  | MNil -> False
  | MCons a _ _ _ -> scalar_is_nnz a

val mat_vec_mul (#n: nat) (m: mat n) (c1: cvec n) : c2: cvec n
  {(mat_is_id m ==> c2 == c1) /\ (vec_is_zero c1 ==> vec_is_zero c2)}

val vec_mat_mul (#n: nat) (r1: rvec n) (m: mat n) : r2: rvec n
  {(mat_is_id m ==> r2 == r1) /\ (vec_is_zero r1 ==> vec_is_zero r2)}

val vec_outer (#n: nat) (c: cvec n) (r: rvec n)
  : m: mat n {(vec_is_zero c \/ vec_is_zero r) ==> mat_is_zero m}

val mat_add (#n: nat) (m1 m2: mat n) : m3: mat n
  {(mat_is_zero m1 ==> m3 == m2) /\ (mat_is_zero m2 ==> m3 == m1)}

val mat_neg (#n: nat) (m: mat n) : mat n

let mat_sub (#n: nat) (m1 m2: mat n) : mat n = mat_add m1 (mat_neg m2)

val mat_mul (#n: nat) (m1 m2: mat n) : r: mat n
  {(mat_is_id m1 ==> r == m2) /\ (mat_is_id m2 ==> r == m1)}

val mat_transpose (#n: nat) (m: mat n) : mat n

let mat_schur (#n: pos) (m: mat n{top_left_nnz m}) : mat (n - 1) =
  let MCons a b c d = m in
  mat_sub d (vec_outer (vec_scalar_div c a) b)

let mat_is_inverse (#n: nat) (l r: mat n) : prop =
  mat_mul r l == mat_id /\ mat_mul l r == mat_id

val mat_vec_mul_cons (#n: nat) (#k: pos{k == n + 1})
    (a: num) (b: rvec n) (c: cvec n) (m: mat n) (x: num) (v: cvec n)
  : Lemma (mat_vec_mul #k (MCons a b c m) (VCons x v)
           == VCons (scalar_add (scalar_mul a x) (vec_dot b v))
                    (vec_add (vec_scalar_mul c x) (mat_vec_mul m v)))
          [SMTPat (mat_vec_mul #k (MCons a b c m) (VCons x v))]

val vec_mat_mul_cons (#n: nat) (#k: pos{k == n + 1})
    (x: num) (r: rvec n) (a: num) (b: rvec n) (c: cvec n) (m: mat n)
  : Lemma (vec_mat_mul #k (VCons x r) (MCons a b c m)
           == VCons (scalar_add (scalar_mul x a) (vec_dot r c))
                    (vec_add (vec_scalar_mul b x) (vec_mat_mul r m)))
          [SMTPat (vec_mat_mul #k (VCons x r) (MCons a b c m))]

val vec_outer_cons (#n: nat) (#k: pos{k == n + 1}) (x: num) (c: cvec n) (y: num) (r: rvec n)
  : Lemma (vec_outer #k (VCons x c) (VCons y r)
           == MCons (scalar_mul x y) (vec_scalar_mul r x) (vec_scalar_mul c y) (vec_outer c r))
          [SMTPat (vec_outer #k (VCons x c) (VCons y r))]

val mat_add_cons (#n: nat) (#k: pos{k == n + 1})
    (a1: num) (b1: rvec n) (c1: cvec n) (m1: mat n)
    (a2: num) (b2: rvec n) (c2: cvec n) (m2: mat n)
  : Lemma (mat_add #k (MCons a1 b1 c1 m1) (MCons a2 b2 c2 m2)
           == MCons (scalar_add a1 a2) (vec_add b1 b2) (vec_add c1 c2) (mat_add m1 m2))
          [SMTPat (mat_add #k (MCons a1 b1 c1 m1) (MCons a2 b2 c2 m2))]

val mat_neg_cons (#n: nat) (#k: pos{k == n + 1}) (a: num) (b: rvec n) (c: cvec n) (m: mat n)
  : Lemma (mat_neg #k (MCons a b c m) == MCons (scalar_neg a) (vec_neg b) (vec_neg c) (mat_neg m))
          [SMTPat (mat_neg #k (MCons a b c m))]

val mat_mul_cons (#n: nat) (#k: pos{k == n + 1})
    (a1: num) (b1: rvec n) (c1: cvec n) (m1: mat n)
    (a2: num) (b2: rvec n) (c2: cvec n) (m2: mat n)
  : Lemma (mat_mul #k (MCons a1 b1 c1 m1) (MCons a2 b2 c2 m2)
           == MCons (scalar_add (scalar_mul a1 a2) (vec_dot b1 c2))
                    (vec_add (vec_scalar_mul b2 a1) (vec_mat_mul b1 m2))
                    (vec_add (vec_scalar_mul c1 a2) (mat_vec_mul m1 c2))
                    (mat_add (vec_outer c1 b2) (mat_mul m1 m2)))
          [SMTPat (mat_mul #k (MCons a1 b1 c1 m1) (MCons a2 b2 c2 m2))]

val mat_transpose_cons (#n: nat) (#k: pos{k == n + 1}) (a: num) (b: rvec n) (c: cvec n) (m: mat n)
  : Lemma (mat_transpose #k (MCons a b c m) == MCons a c b (mat_transpose m))
          [SMTPat (mat_transpose #k (MCons a b c m))]

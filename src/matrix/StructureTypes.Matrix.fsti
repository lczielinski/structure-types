module StructureTypes.Matrix

open StructureTypes.Scalar
open StructureTypes.Vector

(* MCons a b c m is the block matrix [[a, b], [c, m]] *)
noeq type mat : nat -> Type =
  | MNil : mat 0
  | MCons : #n: nat -> num -> rvec n -> cvec n -> mat n -> mat (n + 1)

let rec id_mat (#n: nat) : mat n =
  if n = 0 then MNil else MCons one zero_vec zero_vec (id_mat #(n - 1))

let is_id (#n: nat) (m: mat n) : prop = m == id_mat

let rec zero_mat (#n: nat) : mat n =
  if n = 0 then MNil else MCons zero zero_vec zero_vec (zero_mat #(n - 1))

let is_zero_mat (#n: nat) (m: mat n) : prop = m == zero_mat

let top_left_nnz (#n: nat) (m: mat n) : prop =
  match m with
  | MNil -> False
  | MCons a _ _ _ -> is_nnz a

val mat_vec_mul (#n: nat) (m: mat n) (c1: cvec n) : c2: cvec n
  {(is_id m ==> c2 == c1) /\ (is_zero_vec c1 ==> is_zero_vec c2)}

val vec_mat_mul (#n: nat) (r1: rvec n) (m: mat n) : r2: rvec n
  {(is_id m ==> r2 == r1) /\ (is_zero_vec r1 ==> is_zero_vec r2)}

val outer_prod (#n: nat) (c: cvec n) (r: rvec n)
  : m: mat n {(is_zero_vec c \/ is_zero_vec r) ==> is_zero_mat m}

val mat_add (#n: nat) (m1 m2: mat n) : m3: mat n
  {(is_zero_mat m1 ==> m3 == m2) /\ (is_zero_mat m2 ==> m3 == m1)}

val mat_neg (#n: nat) (m: mat n) : mat n

let mat_sub (#n: nat) (m1 m2: mat n) : mat n = mat_add m1 (mat_neg m2)

val mat_mul (#n: nat) (m1 m2: mat n) : r: mat n
  {(is_id m1 ==> r == m2) /\ (is_id m2 ==> r == m1)}

val transpose (#n: nat) (m: mat n) : mat n

let schur1 (#n: pos) (m: mat n{top_left_nnz m}) : mat (n - 1) =
  let MCons a b c d = m in
  mat_sub d (outer_prod (vec_scalar_div c a) b)

let is_inverse (#n: nat) (l r: mat n) : prop =
  mat_mul r l == id_mat /\ mat_mul l r == id_mat

val mat_vec_mul_cons (#n: nat) (#k: pos{k == n + 1})
    (a: num) (b: rvec n) (c: cvec n) (m: mat n) (x: num) (v: cvec n)
  : Lemma (mat_vec_mul #k (MCons a b c m) (VCons x v)
           == VCons (scalar_add (scalar_mul a x) (inner_prod b v))
                    (vec_add (vec_scalar_mul c x) (mat_vec_mul m v)))
          [SMTPat (mat_vec_mul #k (MCons a b c m) (VCons x v))]

val vec_mat_mul_cons (#n: nat) (#k: pos{k == n + 1})
    (x: num) (r: rvec n) (a: num) (b: rvec n) (c: cvec n) (m: mat n)
  : Lemma (vec_mat_mul #k (VCons x r) (MCons a b c m)
           == VCons (scalar_add (scalar_mul x a) (inner_prod r c))
                    (vec_add (vec_scalar_mul b x) (vec_mat_mul r m)))
          [SMTPat (vec_mat_mul #k (VCons x r) (MCons a b c m))]

val outer_prod_cons (#n: nat) (#k: pos{k == n + 1}) (x: num) (c: cvec n) (y: num) (r: rvec n)
  : Lemma (outer_prod #k (VCons x c) (VCons y r)
           == MCons (scalar_mul x y) (vec_scalar_mul r x) (vec_scalar_mul c y) (outer_prod c r))
          [SMTPat (outer_prod #k (VCons x c) (VCons y r))]

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
           == MCons (scalar_add (scalar_mul a1 a2) (inner_prod b1 c2))
                    (vec_add (vec_scalar_mul b2 a1) (vec_mat_mul b1 m2))
                    (vec_add (vec_scalar_mul c1 a2) (mat_vec_mul m1 c2))
                    (mat_add (outer_prod c1 b2) (mat_mul m1 m2)))
          [SMTPat (mat_mul #k (MCons a1 b1 c1 m1) (MCons a2 b2 c2 m2))]

val transpose_cons (#n: nat) (#k: pos{k == n + 1}) (a: num) (b: rvec n) (c: cvec n) (m: mat n)
  : Lemma (transpose #k (MCons a b c m) == MCons a c b (transpose m))
          [SMTPat (transpose #k (MCons a b c m))]

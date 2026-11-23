module StructureTypes.Matrix.Lemmas

open StructureTypes.Scalar
open StructureTypes.Scalar.Lemmas
open StructureTypes.Vector
open StructureTypes.Vector.Lemmas
open StructureTypes.Matrix

let rec mat_vec_mul_vec_neg (#n: nat) (m: mat n) (c: cvec n)
  : Lemma (mat_vec_mul m (vec_neg c) == vec_neg (mat_vec_mul m c))
          [SMTPat (mat_vec_mul m (vec_neg c))] =
  match m with
  | MNil -> ()
  | MCons _ _ _ m' -> let VCons _ c' = c in mat_vec_mul_vec_neg m' c'

let rec mat_vec_mul_div_scalar (#n: nat) (m: mat n) (c: cvec n) (l: num{is_nnz l})
  : Lemma (vec_scalar_mul (mat_vec_mul m (vec_scalar_div c l)) l == mat_vec_mul m c)
          [SMTPat (vec_scalar_mul (mat_vec_mul m (vec_scalar_div c l)) l)] =
  match m with
  | MNil -> ()
  | MCons a b c' m' ->
    let VCons x v' = c in
    mat_vec_mul_div_scalar m' v' l;
    scalar_mul_assoc a (scalar_div x l) l;
    inner_prod_scalar_r b (vec_scalar_div v' l) l;
    vec_scalar_mul_assoc c' (scalar_div x l) l

let rec outer_prod_div_comm (#n: nat) (c: cvec n) (b: rvec n) (l: num{is_nnz l})
  : Lemma (outer_prod c (vec_scalar_div b l) == outer_prod (vec_scalar_div c l) b)
          [SMTPat (outer_prod c (vec_scalar_div b l))] =
  match c with
  | VNil -> ()
  | VCons x c' ->
    let VCons y b' = b in
    outer_prod_div_comm c' b' l;
    scalar_mul_div_comm x y l;
    vec_scalar_mul_div_comm b' x l;
    vec_scalar_mul_div_comm c' y l

let rec mat_add_sub_cancel (#n: nat) (m1 m2: mat n)
  : Lemma (mat_add m2 (mat_sub m1 m2) == m1) [SMTPat (mat_add m2 (mat_sub m1 m2))] =
  match m1 with
  | MNil -> ()
  | MCons a1 b1 c1 m1' ->
    let MCons a2 b2 c2 m2' = m2 in
    mat_add_sub_cancel m1' m2';
    scalar_add_comm a1 (scalar_neg a2);
    scalar_add_assoc a2 (scalar_neg a2) a1;
    vec_add_sub_cancel b1 b2;
    vec_add_sub_cancel c1 c2

let rec transpose_involutive (#n: nat) (m: mat n)
  : Lemma (transpose (transpose m) == m) [SMTPat (transpose (transpose m))] =
  match m with
  | MNil -> ()
  | MCons _ _ _ m' -> transpose_involutive m'

let rec mat_vec_mul_add_vec (#n: nat) (m: mat n) (v1 v2: cvec n)
  : Lemma (mat_vec_mul m (vec_add v1 v2) == vec_add (mat_vec_mul m v1) (mat_vec_mul m v2)) =
  match m with
  | MNil -> ()
  | MCons a b c m' ->
    let VCons x1 u1 = v1 in
    let VCons x2 u2 = v2 in
    mat_vec_mul_add_vec m' u1 u2;
    scalar_mul_add_dist_l a x1 x2;
    inner_prod_add_r b u1 u2;
    scalar_add_middle_swap (scalar_mul a x1) (scalar_mul a x2) (inner_prod b u1) (inner_prod b u2);
    vec_scalar_mul_add_scalar c x1 x2;
    vec_add_middle_swap (vec_scalar_mul c x1) (vec_scalar_mul c x2) (mat_vec_mul m' u1) (mat_vec_mul m' u2)

let rec mat_vec_mul_scalar (#n: nat) (m: mat n) (v: cvec n) (s: num)
  : Lemma (mat_vec_mul m (vec_scalar_mul v s) == vec_scalar_mul (mat_vec_mul m v) s) =
  match m with
  | MNil -> ()
  | MCons a b c m' ->
    let VCons x u = v in
    mat_vec_mul_scalar m' u s;
    scalar_mul_assoc a x s;
    inner_prod_scalar_r b u s;
    vec_scalar_mul_assoc c x s;
    vec_scalar_mul_add_dist (vec_scalar_mul c x) (mat_vec_mul m' u) s

let rec mat_vec_mul_add_mat (#n: nat) (m1 m2: mat n) (v: cvec n)
  : Lemma (mat_vec_mul (mat_add m1 m2) v == vec_add (mat_vec_mul m1 v) (mat_vec_mul m2 v)) =
  match m1 with
  | MNil -> ()
  | MCons a1 b1 c1 m1' ->
    let MCons a2 b2 c2 m2' = m2 in
    let VCons x u = v in
    mat_vec_mul_add_mat m1' m2' u;
    inner_prod_add_l b1 b2 u;
    scalar_add_middle_swap (scalar_mul a1 x) (scalar_mul a2 x) (inner_prod b1 u) (inner_prod b2 u);
    vec_add_middle_swap (vec_scalar_mul c1 x) (vec_scalar_mul c2 x) (mat_vec_mul m1' u) (mat_vec_mul m2' u)

let rec mat_vec_mul_neg_mat (#n: nat) (m: mat n) (v: cvec n)
  : Lemma (mat_vec_mul (mat_neg m) v == vec_neg (mat_vec_mul m v)) =
  match m with
  | MNil -> ()
  | MCons a b c m' ->
    let VCons x u = v in
    mat_vec_mul_neg_mat m' u;
    scalar_mul_neg_l a x;
    inner_prod_neg_l b u;
    vec_scalar_mul_neg_v c x

let rec mat_vec_mul_outer (#n: nat) (c: cvec n) (r: rvec n) (v: cvec n)
  : Lemma (mat_vec_mul (outer_prod c r) v == vec_scalar_mul c (inner_prod r v)) =
  match c with
  | VNil -> ()
  | VCons p c' ->
    let VCons q r' = r in
    let VCons y v' = v in
    mat_vec_mul_outer c' r' v';
    scalar_mul_assoc p q y;
    inner_prod_scalar_l r' v' p;
    scalar_mul_comm (inner_prod r' v') p;
    scalar_mul_add_dist_l p (scalar_mul q y) (inner_prod r' v');
    vec_scalar_mul_assoc c' q y;
    vec_scalar_mul_add_scalar c' (scalar_mul q y) (inner_prod r' v')

let rec inner_vec_mat_mul (#n: nat) (r: rvec n) (m: mat n) (v: cvec n)
  : Lemma (inner_prod (vec_mat_mul r m) v == inner_prod r (mat_vec_mul m v)) =
  match m with
  | MNil -> ()
  | MCons a b c m' ->
    let VCons s r' = r in
    let VCons x u = v in
    inner_vec_mat_mul r' m' u;
    scalar_mul_add_dist_r (scalar_mul s a) (inner_prod r' c) x;
    inner_prod_add_l (vec_scalar_mul b s) (vec_mat_mul r' m') u;
    scalar_mul_assoc s a x;
    inner_prod_scalar_r r' c x;
    inner_prod_scalar_l b u s;
    scalar_mul_comm (inner_prod b u) s;
    scalar_mul_add_dist_l s (scalar_mul a x) (inner_prod b u);
    inner_prod_add_r r' (vec_scalar_mul c x) (mat_vec_mul m' u);
    scalar_add_middle_swap
      (scalar_mul s (scalar_mul a x)) (inner_prod r' (vec_scalar_mul c x))
      (scalar_mul s (inner_prod b u)) (inner_prod r' (mat_vec_mul m' u))

let rec mat_ext (#n: nat) (m1 m2: mat n)
  : Lemma (requires forall (c: cvec n). mat_vec_mul m1 c == mat_vec_mul m2 c) (ensures m1 == m2) =
  match m1 with
  | MNil -> ()
  | MCons #k a1 b1 c1 m1' ->
    let MCons a2 b2 c2 m2' = m2 in
    let e : cvec n = VCons one (zero_vec #k) in
    assert (mat_vec_mul m1 e == mat_vec_mul m2 e);
    let aux (v: cvec k)
      : Lemma (mat_vec_mul m1' v == mat_vec_mul m2' v /\ inner_prod b1 v == inner_prod b2 v) =
      let e' : cvec n = VCons zero v in
      assert (mat_vec_mul m1 e' == mat_vec_mul m2 e')
    in
    FStar.Classical.forall_intro aux;
    mat_ext m1' m2';
    vec_ext b1 b2

let rec mat_vec_mul_assoc (#n: nat) (m1 m2: mat n) (v: cvec n)
  : Lemma (mat_vec_mul (mat_mul m1 m2) v == mat_vec_mul m1 (mat_vec_mul m2 v))
          [SMTPat (mat_vec_mul m1 (mat_vec_mul m2 v)); SMTPat (mat_mul m1 m2)] =
  match m1 with
  | MNil -> ()
  | MCons a1 b1 c1 m1' ->
    let MCons a2 b2 c2 m2' = m2 in
    let VCons x v' = v in
    mat_vec_mul_assoc m1' m2' v';
    let s1 = scalar_mul (scalar_mul a1 a2) x in
    let s2 = scalar_mul (inner_prod b1 c2) x in
    let s3 = scalar_mul (inner_prod b2 v') a1 in
    let s4 = inner_prod b1 (mat_vec_mul m2' v') in
    scalar_mul_add_dist_r (scalar_mul a1 a2) (inner_prod b1 c2) x;
    inner_prod_add_l (vec_scalar_mul b2 a1) (vec_mat_mul b1 m2') v';
    inner_prod_scalar_l b2 v' a1;
    inner_vec_mat_mul b1 m2' v';
    scalar_mul_add_dist_l a1 (scalar_mul a2 x) (inner_prod b2 v');
    scalar_mul_assoc a1 a2 x;
    scalar_mul_comm a1 (inner_prod b2 v');
    inner_prod_add_r b1 (vec_scalar_mul c2 x) (mat_vec_mul m2' v');
    inner_prod_scalar_r b1 c2 x;
    scalar_add_middle_swap s1 s2 s3 s4;
    let w1 = vec_scalar_mul c1 (scalar_mul a2 x) in
    let w2 = vec_scalar_mul (mat_vec_mul m1' c2) x in
    let w3 = vec_scalar_mul c1 (inner_prod b2 v') in
    let w4 = mat_vec_mul m1' (mat_vec_mul m2' v') in
    vec_scalar_mul_add_dist (vec_scalar_mul c1 a2) (mat_vec_mul m1' c2) x;
    vec_scalar_mul_assoc c1 a2 x;
    mat_vec_mul_add_mat (outer_prod c1 b2) (mat_mul m1' m2') v';
    mat_vec_mul_outer c1 b2 v';
    vec_scalar_mul_add_scalar c1 (scalar_mul a2 x) (inner_prod b2 v');
    mat_vec_mul_add_vec m1' (vec_scalar_mul c2 x) (mat_vec_mul m2' v');
    mat_vec_mul_scalar m1' c2 x;
    vec_add_middle_swap w1 w2 w3 w4

let mat_mul_assoc (#n: nat) (a b c: mat n)
  : Lemma (mat_mul (mat_mul a b) c == mat_mul a (mat_mul b c)) =
  let aux (x: cvec n)
    : Lemma (mat_vec_mul (mat_mul (mat_mul a b) c) x == mat_vec_mul (mat_mul a (mat_mul b c)) x) =
    mat_vec_mul_assoc (mat_mul a b) c x;
    mat_vec_mul_assoc a b (mat_vec_mul c x);
    mat_vec_mul_assoc b c x;
    mat_vec_mul_assoc a (mat_mul b c) x
  in
  FStar.Classical.forall_intro aux;
  mat_ext (mat_mul (mat_mul a b) c) (mat_mul a (mat_mul b c))

let mat_mul_sub_distr (#n: nat) (m m1 m2: mat n)
  : Lemma (mat_mul m (mat_sub m1 m2) == mat_sub (mat_mul m m1) (mat_mul m m2))
          [SMTPat (mat_mul m (mat_sub m1 m2))] =
  let lhs = mat_mul m (mat_sub m1 m2) in
  let rhs = mat_sub (mat_mul m m1) (mat_mul m m2) in
  let aux (x: cvec n) : Lemma (mat_vec_mul lhs x == mat_vec_mul rhs x) =
    mat_vec_mul_assoc m (mat_sub m1 m2) x;
    mat_vec_mul_add_mat m1 (mat_neg m2) x;
    mat_vec_mul_neg_mat m2 x;
    mat_vec_mul_add_vec m (mat_vec_mul m1 x) (vec_neg (mat_vec_mul m2 x));
    mat_vec_mul_add_mat (mat_mul m m1) (mat_neg (mat_mul m m2)) x;
    mat_vec_mul_neg_mat (mat_mul m m2) x;
    mat_vec_mul_assoc m m1 x;
    mat_vec_mul_assoc m m2 x
  in
  FStar.Classical.forall_intro aux;
  mat_ext lhs rhs

let mat_mul_outer_prod (#n: nat) (m: mat n) (c: cvec n) (r: rvec n)
  : Lemma (mat_mul m (outer_prod c r) == outer_prod (mat_vec_mul m c) r)
          [SMTPat (mat_mul m (outer_prod c r))] =
  let lhs = mat_mul m (outer_prod c r) in
  let rhs = outer_prod (mat_vec_mul m c) r in
  let aux (x: cvec n) : Lemma (mat_vec_mul lhs x == mat_vec_mul rhs x) =
    mat_vec_mul_assoc m (outer_prod c r) x;
    mat_vec_mul_outer c r x;
    mat_vec_mul_scalar m c (inner_prod r x);
    mat_vec_mul_outer (mat_vec_mul m c) r x
  in
  FStar.Classical.forall_intro aux;
  mat_ext lhs rhs

let mat_mul_inv_cancel (#n: nat) (a b c m: mat n)
  : Lemma (requires mat_mul b c == id_mat)
          (ensures mat_mul (mat_mul a b) (mat_mul c m) == mat_mul a m)
          [SMTPat (mat_mul (mat_mul a b) (mat_mul c m))] =
  mat_mul_assoc a b (mat_mul c m);
  mat_mul_assoc b c m

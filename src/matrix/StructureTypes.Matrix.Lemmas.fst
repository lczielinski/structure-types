module StructureTypes.Matrix.Lemmas

open StructureTypes.Scalar
open StructureTypes.Scalar.Lemmas
open StructureTypes.Vector
open StructureTypes.Vector.Lemmas
open StructureTypes.Matrix

let rec mat_vec_mul_neg_r (#n: nat) (m: mat n) (c: cvec n)
  : Lemma (mat_vec_mul m (vec_neg c) == vec_neg (mat_vec_mul m c))
          [SMTPat (mat_vec_mul m (vec_neg c))] =
  match m with
  | MNil -> ()
  | MCons _ _ _ m' -> let VCons _ c' = c in mat_vec_mul_neg_r m' c'

let rec mat_vec_mul_scalar_div_cancel (#n: nat) (m: mat n) (c: cvec n) (l: num{scalar_is_nnz l})
  : Lemma (vec_scalar_mul (mat_vec_mul m (vec_scalar_div c l)) l == mat_vec_mul m c)
          [SMTPat (vec_scalar_mul (mat_vec_mul m (vec_scalar_div c l)) l)] =
  match m with
  | MNil -> ()
  | MCons a b c' m' ->
    let VCons x v' = c in
    mat_vec_mul_scalar_div_cancel m' v' l;
    scalar_mul_assoc a (scalar_div x l) l;
    vec_dot_scalar_mul_r b (vec_scalar_div v' l) l;
    vec_scalar_mul_assoc c' (scalar_div x l) l

let rec vec_outer_div_comm (#n: nat) (c: cvec n) (b: rvec n) (l: num{scalar_is_nnz l})
  : Lemma (vec_outer c (vec_scalar_div b l) == vec_outer (vec_scalar_div c l) b)
          [SMTPat (vec_outer c (vec_scalar_div b l))] =
  match c with
  | VNil -> ()
  | VCons x c' ->
    let VCons y b' = b in
    vec_outer_div_comm c' b' l;
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

let rec mat_transpose_involutive (#n: nat) (m: mat n)
  : Lemma (mat_transpose (mat_transpose m) == m) [SMTPat (mat_transpose (mat_transpose m))] =
  match m with
  | MNil -> ()
  | MCons _ _ _ m' -> mat_transpose_involutive m'

let rec mat_vec_mul_add_r (#n: nat) (m: mat n) (v1 v2: cvec n)
  : Lemma (mat_vec_mul m (vec_add v1 v2) == vec_add (mat_vec_mul m v1) (mat_vec_mul m v2)) =
  match m with
  | MNil -> ()
  | MCons a b c m' ->
    let VCons x1 u1 = v1 in
    let VCons x2 u2 = v2 in
    mat_vec_mul_add_r m' u1 u2;
    scalar_mul_add_r a x1 x2;
    vec_dot_add_r b u1 u2;
    scalar_add_middle_swap (scalar_mul a x1) (scalar_mul a x2) (vec_dot b u1) (vec_dot b u2);
    vec_scalar_mul_add_r c x1 x2;
    vec_add_middle_swap (vec_scalar_mul c x1) (vec_scalar_mul c x2) (mat_vec_mul m' u1) (mat_vec_mul m' u2)

let rec mat_vec_mul_scalar_mul_r (#n: nat) (m: mat n) (v: cvec n) (s: num)
  : Lemma (mat_vec_mul m (vec_scalar_mul v s) == vec_scalar_mul (mat_vec_mul m v) s) =
  match m with
  | MNil -> ()
  | MCons a b c m' ->
    let VCons x u = v in
    mat_vec_mul_scalar_mul_r m' u s;
    scalar_mul_assoc a x s;
    vec_dot_scalar_mul_r b u s;
    vec_scalar_mul_assoc c x s;
    vec_scalar_mul_add_l (vec_scalar_mul c x) (mat_vec_mul m' u) s

let rec mat_vec_mul_add_l (#n: nat) (m1 m2: mat n) (v: cvec n)
  : Lemma (mat_vec_mul (mat_add m1 m2) v == vec_add (mat_vec_mul m1 v) (mat_vec_mul m2 v)) =
  match m1 with
  | MNil -> ()
  | MCons a1 b1 c1 m1' ->
    let MCons a2 b2 c2 m2' = m2 in
    let VCons x u = v in
    mat_vec_mul_add_l m1' m2' u;
    vec_dot_add_l b1 b2 u;
    scalar_add_middle_swap (scalar_mul a1 x) (scalar_mul a2 x) (vec_dot b1 u) (vec_dot b2 u);
    vec_add_middle_swap (vec_scalar_mul c1 x) (vec_scalar_mul c2 x) (mat_vec_mul m1' u) (mat_vec_mul m2' u)

let rec mat_vec_mul_neg_l (#n: nat) (m: mat n) (v: cvec n)
  : Lemma (mat_vec_mul (mat_neg m) v == vec_neg (mat_vec_mul m v)) =
  match m with
  | MNil -> ()
  | MCons a b c m' ->
    let VCons x u = v in
    mat_vec_mul_neg_l m' u;
    scalar_mul_neg_l a x;
    vec_dot_neg_l b u;
    vec_scalar_mul_neg_l c x

let rec mat_vec_mul_vec_outer_l (#n: nat) (c: cvec n) (r: rvec n) (v: cvec n)
  : Lemma (mat_vec_mul (vec_outer c r) v == vec_scalar_mul c (vec_dot r v)) =
  match c with
  | VNil -> ()
  | VCons p c' ->
    let VCons q r' = r in
    let VCons y v' = v in
    mat_vec_mul_vec_outer_l c' r' v';
    scalar_mul_assoc p q y;
    vec_dot_scalar_mul_l r' v' p;
    scalar_mul_comm (vec_dot r' v') p;
    scalar_mul_add_r p (scalar_mul q y) (vec_dot r' v');
    vec_scalar_mul_assoc c' q y;
    vec_scalar_mul_add_r c' (scalar_mul q y) (vec_dot r' v')

let rec vec_dot_vec_mat_mul_l (#n: nat) (r: rvec n) (m: mat n) (v: cvec n)
  : Lemma (vec_dot (vec_mat_mul r m) v == vec_dot r (mat_vec_mul m v)) =
  match m with
  | MNil -> ()
  | MCons a b c m' ->
    let VCons s r' = r in
    let VCons x u = v in
    vec_dot_vec_mat_mul_l r' m' u;
    scalar_mul_add_l (scalar_mul s a) (vec_dot r' c) x;
    vec_dot_add_l (vec_scalar_mul b s) (vec_mat_mul r' m') u;
    scalar_mul_assoc s a x;
    vec_dot_scalar_mul_r r' c x;
    vec_dot_scalar_mul_l b u s;
    scalar_mul_comm (vec_dot b u) s;
    scalar_mul_add_r s (scalar_mul a x) (vec_dot b u);
    vec_dot_add_r r' (vec_scalar_mul c x) (mat_vec_mul m' u);
    scalar_add_middle_swap
      (scalar_mul s (scalar_mul a x)) (vec_dot r' (vec_scalar_mul c x))
      (scalar_mul s (vec_dot b u)) (vec_dot r' (mat_vec_mul m' u))

let rec mat_ext (#n: nat) (m1 m2: mat n)
  : Lemma (requires forall (c: cvec n). mat_vec_mul m1 c == mat_vec_mul m2 c) (ensures m1 == m2) =
  match m1 with
  | MNil -> ()
  | MCons #k a1 b1 c1 m1' ->
    let MCons a2 b2 c2 m2' = m2 in
    let e : cvec n = VCons scalar_one (vec_zero #k) in
    assert (mat_vec_mul m1 e == mat_vec_mul m2 e);
    let aux (v: cvec k)
      : Lemma (mat_vec_mul m1' v == mat_vec_mul m2' v /\ vec_dot b1 v == vec_dot b2 v) =
      let e' : cvec n = VCons scalar_zero v in
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
    let s2 = scalar_mul (vec_dot b1 c2) x in
    let s3 = scalar_mul (vec_dot b2 v') a1 in
    let s4 = vec_dot b1 (mat_vec_mul m2' v') in
    scalar_mul_add_l (scalar_mul a1 a2) (vec_dot b1 c2) x;
    vec_dot_add_l (vec_scalar_mul b2 a1) (vec_mat_mul b1 m2') v';
    vec_dot_scalar_mul_l b2 v' a1;
    vec_dot_vec_mat_mul_l b1 m2' v';
    scalar_mul_add_r a1 (scalar_mul a2 x) (vec_dot b2 v');
    scalar_mul_assoc a1 a2 x;
    scalar_mul_comm a1 (vec_dot b2 v');
    vec_dot_add_r b1 (vec_scalar_mul c2 x) (mat_vec_mul m2' v');
    vec_dot_scalar_mul_r b1 c2 x;
    scalar_add_middle_swap s1 s2 s3 s4;
    let w1 = vec_scalar_mul c1 (scalar_mul a2 x) in
    let w2 = vec_scalar_mul (mat_vec_mul m1' c2) x in
    let w3 = vec_scalar_mul c1 (vec_dot b2 v') in
    let w4 = mat_vec_mul m1' (mat_vec_mul m2' v') in
    vec_scalar_mul_add_l (vec_scalar_mul c1 a2) (mat_vec_mul m1' c2) x;
    vec_scalar_mul_assoc c1 a2 x;
    mat_vec_mul_add_l (vec_outer c1 b2) (mat_mul m1' m2') v';
    mat_vec_mul_vec_outer_l c1 b2 v';
    vec_scalar_mul_add_r c1 (scalar_mul a2 x) (vec_dot b2 v');
    mat_vec_mul_add_r m1' (vec_scalar_mul c2 x) (mat_vec_mul m2' v');
    mat_vec_mul_scalar_mul_r m1' c2 x;
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

let mat_mul_sub_r (#n: nat) (m m1 m2: mat n)
  : Lemma (mat_mul m (mat_sub m1 m2) == mat_sub (mat_mul m m1) (mat_mul m m2))
          [SMTPat (mat_mul m (mat_sub m1 m2))] =
  let lhs = mat_mul m (mat_sub m1 m2) in
  let rhs = mat_sub (mat_mul m m1) (mat_mul m m2) in
  let aux (x: cvec n) : Lemma (mat_vec_mul lhs x == mat_vec_mul rhs x) =
    mat_vec_mul_assoc m (mat_sub m1 m2) x;
    mat_vec_mul_add_l m1 (mat_neg m2) x;
    mat_vec_mul_neg_l m2 x;
    mat_vec_mul_add_r m (mat_vec_mul m1 x) (vec_neg (mat_vec_mul m2 x));
    mat_vec_mul_add_l (mat_mul m m1) (mat_neg (mat_mul m m2)) x;
    mat_vec_mul_neg_l (mat_mul m m2) x;
    mat_vec_mul_assoc m m1 x;
    mat_vec_mul_assoc m m2 x
  in
  FStar.Classical.forall_intro aux;
  mat_ext lhs rhs

let mat_mul_vec_outer_r (#n: nat) (m: mat n) (c: cvec n) (r: rvec n)
  : Lemma (mat_mul m (vec_outer c r) == vec_outer (mat_vec_mul m c) r)
          [SMTPat (mat_mul m (vec_outer c r))] =
  let lhs = mat_mul m (vec_outer c r) in
  let rhs = vec_outer (mat_vec_mul m c) r in
  let aux (x: cvec n) : Lemma (mat_vec_mul lhs x == mat_vec_mul rhs x) =
    mat_vec_mul_assoc m (vec_outer c r) x;
    mat_vec_mul_vec_outer_l c r x;
    mat_vec_mul_scalar_mul_r m c (vec_dot r x);
    mat_vec_mul_vec_outer_l (mat_vec_mul m c) r x
  in
  FStar.Classical.forall_intro aux;
  mat_ext lhs rhs

let mat_mul_inverse_cancel (#n: nat) (a b c m: mat n)
  : Lemma (requires mat_mul b c == mat_id)
          (ensures mat_mul (mat_mul a b) (mat_mul c m) == mat_mul a m)
          [SMTPat (mat_mul (mat_mul a b) (mat_mul c m))] =
  mat_mul_assoc a b (mat_mul c m);
  mat_mul_assoc b c m

let rec mat_add_comm (#n: nat) (m1 m2: mat n) : Lemma (mat_add m1 m2 == mat_add m2 m1) =
  match m1 with
  | MNil -> ()
  | MCons a1 b1 c1 m1' ->
    let MCons a2 b2 c2 m2' = m2 in
    mat_add_comm m1' m2';
    scalar_add_comm a1 a2;
    vec_add_comm b1 b2;
    vec_add_comm c1 c2

let rec mat_neg_involutive (#n: nat) (m: mat n)
  : Lemma (mat_neg (mat_neg m) == m) [SMTPat (mat_neg (mat_neg m))] =
  match m with
  | MNil -> ()
  | MCons _ _ _ m' -> mat_neg_involutive m'

let mat_mul_sub_l (#n: nat) (m1 m2 m: mat n)
  : Lemma (mat_mul (mat_sub m1 m2) m == mat_sub (mat_mul m1 m) (mat_mul m2 m))
          [SMTPat (mat_mul (mat_sub m1 m2) m)] =
  let lhs = mat_mul (mat_sub m1 m2) m in
  let rhs = mat_sub (mat_mul m1 m) (mat_mul m2 m) in
  let aux (x: cvec n) : Lemma (mat_vec_mul lhs x == mat_vec_mul rhs x) =
    mat_vec_mul_assoc (mat_sub m1 m2) m x;
    mat_vec_mul_add_l m1 (mat_neg m2) (mat_vec_mul m x);
    mat_vec_mul_neg_l m2 (mat_vec_mul m x);
    mat_vec_mul_add_l (mat_mul m1 m) (mat_neg (mat_mul m2 m)) x;
    mat_vec_mul_neg_l (mat_mul m2 m) x;
    mat_vec_mul_assoc m1 m x;
    mat_vec_mul_assoc m2 m x
  in
  FStar.Classical.forall_intro aux;
  mat_ext lhs rhs

let vec_outer_vec_mat_mul_r (#n: nat) (c: cvec n) (r: rvec n) (m: mat n)
  : Lemma (vec_outer c (vec_mat_mul r m) == mat_mul (vec_outer c r) m) =
  let lhs = vec_outer c (vec_mat_mul r m) in
  let rhs = mat_mul (vec_outer c r) m in
  let aux (x: cvec n) : Lemma (mat_vec_mul lhs x == mat_vec_mul rhs x) =
    mat_vec_mul_vec_outer_l c (vec_mat_mul r m) x;
    vec_dot_vec_mat_mul_l r m x;
    mat_vec_mul_assoc (vec_outer c r) m x;
    mat_vec_mul_vec_outer_l c r (mat_vec_mul m x)
  in
  FStar.Classical.forall_intro aux;
  mat_ext lhs rhs

let vec_outer_neg_r (#n: nat) (c: cvec n) (r: rvec n)
  : Lemma (vec_outer c (vec_neg r) == mat_neg (vec_outer c r)) =
  let lhs = vec_outer c (vec_neg r) in
  let rhs = mat_neg (vec_outer c r) in
  let aux (x: cvec n) : Lemma (mat_vec_mul lhs x == mat_vec_mul rhs x) =
    mat_vec_mul_vec_outer_l c (vec_neg r) x;
    vec_dot_neg_l r x;
    mat_vec_mul_neg_l (vec_outer c r) x;
    mat_vec_mul_vec_outer_l c r x
  in
  FStar.Classical.forall_intro aux;
  mat_ext lhs rhs

let vec_outer_neg_l (#n: nat) (c: cvec n) (r: rvec n)
  : Lemma (vec_outer (vec_neg c) r == mat_neg (vec_outer c r)) =
  let lhs = vec_outer (vec_neg c) r in
  let rhs = mat_neg (vec_outer c r) in
  let aux (x: cvec n) : Lemma (mat_vec_mul lhs x == mat_vec_mul rhs x) =
    mat_vec_mul_vec_outer_l (vec_neg c) r x;
    vec_scalar_mul_neg_l c (vec_dot r x);
    mat_vec_mul_neg_l (vec_outer c r) x;
    mat_vec_mul_vec_outer_l c r x
  in
  FStar.Classical.forall_intro aux;
  mat_ext lhs rhs

let mat_schur_inverse (#n: nat) (#k: pos{k == n + 1})
    (a: num{scalar_is_nnz a}) (b: rvec n) (c: cvec n) (d: mat n)
    (alpha: num) (beta: rvec n) (gamma: cvec n) (delta: mat n)
  : Lemma (requires mat_is_inverse #k (MCons a b c d) (MCons alpha beta gamma delta))
          (ensures mat_is_inverse #n (mat_schur #k (MCons a b c d)) delta) =
  mat_mul_cons #n #k a b c d alpha beta gamma delta;
  mat_mul_cons #n #k alpha beta gamma delta a b c d;
  let ca = vec_scalar_div c a in
  vec_neg_unique (vec_scalar_mul beta a) (vec_mat_mul b delta);
  vec_scalar_mul_div_cancel beta a;
  vec_outer_div_comm c (vec_scalar_mul beta a) a;
  vec_outer_neg_r ca (vec_scalar_mul beta a);
  vec_outer_vec_mat_mul_r ca b delta;
  mat_mul_sub_l d (vec_outer ca b) delta;
  mat_add_comm (mat_mul d delta) (vec_outer c beta);
  mat_mul_sub_r delta d (vec_outer ca b);
  mat_mul_vec_outer_r delta ca b;
  mat_vec_mul_scalar_div_cancel delta c a;
  vec_scalar_mul_div_cancel (mat_vec_mul delta ca) a;
  vec_neg_unique (vec_scalar_mul gamma a) (mat_vec_mul delta c);
  vec_outer_div_comm (mat_vec_mul delta c) b a;
  vec_outer_neg_l (vec_scalar_mul gamma a) (vec_scalar_div b a);
  vec_outer_div_comm (vec_scalar_mul gamma a) b a;
  vec_scalar_mul_div_cancel gamma a;
  mat_add_comm (mat_mul delta d) (vec_outer gamma b)

let rec mat_transpose_add (#n: nat) (m1 m2: mat n)
  : Lemma (mat_transpose (mat_add m1 m2) == mat_add (mat_transpose m1) (mat_transpose m2)) =
  match m1 with
  | MNil -> ()
  | MCons _ _ _ m1' -> let MCons _ _ _ m2' = m2 in mat_transpose_add m1' m2'

let rec mat_transpose_neg (#n: nat) (m: mat n)
  : Lemma (mat_transpose (mat_neg m) == mat_neg (mat_transpose m)) =
  match m with
  | MNil -> ()
  | MCons _ _ _ m' -> mat_transpose_neg m'

let rec mat_transpose_vec_outer (#n: nat) (c: cvec n) (r: rvec n)
  : Lemma (mat_transpose (vec_outer c r) == vec_outer r c) =
  match c with
  | VNil -> ()
  | VCons x c' -> let VCons y r' = r in mat_transpose_vec_outer c' r'; scalar_mul_comm x y

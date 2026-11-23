module StructureTypes.MatMul

open StructureTypes.Scalar
open StructureTypes.Vector
open StructureTypes.MatrixType
open StructureTypes.Matrix

let triangular_compat (#n: pos) (m1 m2: mat n) : prop =
  (lower m1 /\ lower m2) \/ (upper m1 /\ upper m2)

let rec mat_mul (#n: pos) (m1 m2: mat n) : r: mat n 
  {(lower m1 /\ lower m2 ==> lower r) /\
    (upper m1 /\ upper m2 ==> upper r) /\
    (triangular_compat m1 m2 /\ unit_diag m1 /\ unit_diag m2 ==> unit_diag r) /\
    (triangular_compat m1 m2 /\ pos_diag m1 /\ pos_diag m2 ==> pos_diag r) /\
    (triangular_compat m1 m2 /\ nnz_diag m1 /\ nnz_diag m2 ==> nnz_diag r) /\
    (is_id m1 ==> r == m2) /\ (is_id m2 ==> r == m1)} =
  match m1 with
  | Mat1 a -> let Mat1 b = m2 in Mat1 (scalar_mul a b)
  | MatN m1' c1 a1 b1 ->
    let MatN m2' c2 a2 b2 = m2 in
    MatN (mat_add (outer_prod c1 b2) (mat_mul m1' m2'))
      (vec_add (vec_scalar_mul c1 a2) (mat_vec_mul m1' c2))
      (scalar_add (scalar_mul a1 a2) (inner_prod b1 c2))
      (vec_add (vec_scalar_mul b2 a1) (vec_mat_mul b1 m2'))

(* mul associates *)
let rec mat_vec_mul_assoc (#n:pos) (m1 m2:mat n) (c:cvec n)
  : Lemma (ensures mat_vec_mul (mat_mul m1 m2) c == mat_vec_mul m1 (mat_vec_mul m2 c))
          [SMTPat (mat_vec_mul m1 (mat_vec_mul m2 c)); SMTPat (mat_mul m1 m2)] =
  match m1 with
  | Mat1 a1 -> let Mat1 a2 = m2 in let Vec1 x = c in scalar_mul_assoc a1 a2 x
  | MatN a c1 a1 b1 ->
    let MatN b c2 a2 b2 = m2 in
    let VecN x' x = c in
    mat_vec_mul_assoc a b x';
    (* top block: (U + V) + (W + X) == (V + X) + (U + W) *)
    let u = vec_scalar_mul c1 (inner_prod b2 x') in
    let v = mat_vec_mul a (mat_vec_mul b x') in
    let w = vec_scalar_mul c1 (scalar_mul a2 x) in
    let xx = vec_scalar_mul (mat_vec_mul a c2) x in
    mat_vec_mul_add_mat (outer_prod c1 b2) (mat_mul a b) x';
    mat_vec_mul_outer c1 b2 x';
    vec_scalar_mul_add_dist (vec_scalar_mul c1 a2) (mat_vec_mul a c2) x;
    vec_scalar_mul_assoc c1 a2 x;
    mat_vec_mul_add_vec a (mat_vec_mul b x') (vec_scalar_mul c2 x);
    mat_vec_mul_scalar a c2 x;
    vec_scalar_mul_add_scalar c1 (inner_prod b2 x') (scalar_mul a2 x);
    vec_add_middle_swap u v w xx;
    vec_add_comm (vec_add u w) (vec_add v xx);
    (* corner: (S1 + S2) + (S3 + S4) == (S2 + S4) + (S1 + S3) *)
    let s1 = scalar_mul (inner_prod b2 x') a1 in
    let s2 = inner_prod b1 (mat_vec_mul b x') in
    let s3 = scalar_mul (scalar_mul a1 a2) x in
    let s4 = scalar_mul (inner_prod b1 c2) x in
    inner_prod_add_l (vec_scalar_mul b2 a1) (vec_mat_mul b1 b) x';
    inner_prod_scalar_l b2 x' a1;
    inner_vec_mat_mul b1 b x';
    scalar_mul_add_dist_r (scalar_mul a1 a2) (inner_prod b1 c2) x;
    inner_prod_add_r b1 (mat_vec_mul b x') (vec_scalar_mul c2 x);
    inner_prod_scalar_r b1 c2 x;
    scalar_mul_add_dist_l a1 (inner_prod b2 x') (scalar_mul a2 x);
    scalar_mul_comm a1 (inner_prod b2 x');
    scalar_mul_assoc a1 a2 x;
    scalar_add_middle_swap s1 s2 s3 s4;
    scalar_add_comm (scalar_add s1 s3) (scalar_add s2 s4)

let mat_mul_assoc (#n:pos) (a b c:mat n)
  : Lemma (mat_mul (mat_mul a b) c == mat_mul a (mat_mul b c)) =
  let aux (x:cvec n)
    : Lemma (mat_vec_mul (mat_mul (mat_mul a b) c) x == mat_vec_mul (mat_mul a (mat_mul b c)) x) =
    mat_vec_mul_assoc (mat_mul a b) c x;
    mat_vec_mul_assoc a b (mat_vec_mul c x);
    mat_vec_mul_assoc b c x;
    mat_vec_mul_assoc a (mat_mul b c) x
  in
  FStar.Classical.forall_intro aux;
  mat_ext (mat_mul (mat_mul a b) c) (mat_mul a (mat_mul b c))

(* inverses *)
let is_inverse (#n:pos) (l r:mat n) : prop =
  (mat_mul r l == id_mat) /\ (mat_mul l r == id_mat)

assume val mat_mul_perm (#n: pos) (m1 m2: mat n)
    : Lemma (requires perm m1 /\ perm m2)
      (ensures perm (mat_mul m1 m2))
      [SMTPat (perm (mat_mul m1 m2))]

let mat_mul_sub_distr (#n: pos) (m m1 m2: mat n)
    : Lemma (mat_mul m (mat_sub m1 m2) == mat_sub (mat_mul m m1) (mat_mul m m2))
      [SMTPat (mat_mul m (mat_sub m1 m2))] =
  let lhs = mat_mul m (mat_sub m1 m2) in
  let rhs = mat_sub (mat_mul m m1) (mat_mul m m2) in
  let aux (x: cvec n) : Lemma (mat_vec_mul lhs x == mat_vec_mul rhs x) =
    mat_vec_mul_assoc m (mat_sub m1 m2) x;
    mat_vec_mul_add_mat m1 (mat_neg m2) x;
    mat_vec_mul_neg_mat m2 x;
    mat_vec_mul_add_vec m (mat_vec_mul m1 x) (vec_neg (mat_vec_mul m2 x));
    mat_vec_mul_vec_neg m (mat_vec_mul m2 x);
    mat_vec_mul_add_mat (mat_mul m m1) (mat_neg (mat_mul m m2)) x;
    mat_vec_mul_neg_mat (mat_mul m m2) x;
    mat_vec_mul_assoc m m1 x;
    mat_vec_mul_assoc m m2 x
  in
  FStar.Classical.forall_intro aux;
  mat_ext lhs rhs

let mat_mul_outer_prod (#n: pos) (m: mat n) (c: cvec n) (r: rvec n)
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

assume val transpose_perm : #n:pos -> m:mat n ->
  Lemma (requires perm m)
        (ensures perm (transpose m) /\
                 mat_mul m (transpose m) == id_mat /\
                 mat_mul (transpose m) m == id_mat)
        [SMTPat (perm m)]

let mat_mul_inv_cancel (#n:pos) (a b c m:mat n)
  : Lemma (requires mat_mul b c == id_mat)
          (ensures mat_mul (mat_mul a b) (mat_mul c m) == mat_mul a m)
          [SMTPat (mat_mul (mat_mul a b) (mat_mul c m))] =
  mat_mul_assoc a b (mat_mul c m);
  mat_mul_assoc b c m

let mul_augment (#n:pos)
  (m1:mat n) (c1:cvec n) (a1:num) (b1:rvec n)
  (m2:mat n) (c2:cvec n) (a2:num) (b2:rvec n) :
  Lemma (ensures mat_mul (MatN m1 c1 a1 b1) (MatN m2 c2 a2 b2)
              == MatN (mat_add (outer_prod c1 b2) (mat_mul m1 m2))
                         (vec_add (vec_scalar_mul c1 a2) (mat_vec_mul m1 c2))
                         (scalar_add (scalar_mul a1 a2) (inner_prod b1 c2))
                         (vec_add (vec_scalar_mul b2 a1) (vec_mat_mul b1 m2)))
        [SMTPat (mat_mul (MatN m1 c1 a1 b1) (MatN m2 c2 a2 b2))] = ()

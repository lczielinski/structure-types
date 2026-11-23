module StructureTypes.Props.Spd

open StructureTypes.Scalar
open StructureTypes.Scalar.Lemmas
open StructureTypes.Vector
open StructureTypes.Vector.Lemmas
open StructureTypes.Matrix
open StructureTypes.Matrix.Lemmas
open StructureTypes.Shape

let quad (#n: nat) (m: mat n) (x: cvec n) : num = vec_dot x (mat_vec_mul m x)

let spd #n m = symmetric m /\ (forall (x: cvec n). ~(vec_is_zero x) ==> scalar_is_pos (quad m x))

let spd_at (#n: nat) (m: mat n) (x: cvec n)
  : Lemma (requires spd m /\ ~(vec_is_zero x)) (ensures scalar_is_pos (quad m x)) = ()

let spd_symmetric #n m = ()

let spd_cons #n #k a b c m =
  let mm : mat k = MCons a b c m in
  scalar_one_pos scalar_one;
  spd_at mm (VCons scalar_one (vec_zero #n));
  let aux (y: cvec n) : Lemma (requires ~(vec_is_zero y)) (ensures scalar_is_pos (quad m y)) =
    spd_at mm (VCons scalar_zero y)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let rec spd_pos_diag #n m =
  match m with
  | MNil -> ()
  | MCons a b c m' -> spd_cons #_ #n a b c m'; spd_pos_diag m'

let schur_quad (#n: nat) (#k: pos{k == n + 1}) (a: num{scalar_is_pos a}) (b: rvec n) (d: mat n) (y: cvec n)
  : Lemma (let s = vec_dot b y in
           let t = scalar_neg (scalar_div s a) in
           quad (mat_sub d (vec_outer (vec_scalar_div b a) b)) y == quad #k (MCons a b b d) (VCons t y)) =
  let s = vec_dot b y in
  let sa = scalar_div s a in
  let t = scalar_neg sa in
  let ba = vec_scalar_div b a in
  scalar_mul_neg_r a sa;
  vec_dot_add_r y (vec_scalar_mul b t) (mat_vec_mul d y);
  vec_dot_comm y b;
  scalar_mul_neg_r s sa;
  scalar_mul_comm s sa;
  mat_vec_mul_add_l d (mat_neg (vec_outer ba b)) y;
  mat_vec_mul_neg_l (vec_outer ba b) y;
  mat_vec_mul_vec_outer_l ba b y;
  vec_dot_add_r y (mat_vec_mul d y) (vec_neg (vec_scalar_mul ba s));
  vec_dot_scalar_mul_r y ba a;
  scalar_mul_cancel_r (vec_dot y ba) sa a;
  scalar_add_comm (scalar_neg (scalar_mul sa s)) (vec_dot y (mat_vec_mul d y))

let spd_mat_schur #n #k m =
  let MCons a b c d = m in
  spd_cons #k #n a b c d;
  let ba = vec_scalar_div b a in
  mat_transpose_add d (mat_neg (vec_outer ba b));
  mat_transpose_neg (vec_outer ba b);
  mat_transpose_vec_outer ba b;
  vec_outer_div_comm b b a;
  let aux (y: cvec k) : Lemma (requires ~(vec_is_zero y)) (ensures scalar_is_pos (quad (mat_schur m) y)) =
    schur_quad #k #n a b d y;
    spd_at m (VCons (scalar_neg (scalar_div (vec_dot b y) a)) y)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

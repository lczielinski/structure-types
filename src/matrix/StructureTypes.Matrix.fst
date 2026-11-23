module StructureTypes.Matrix

open StructureTypes.Scalar
open StructureTypes.Vector

let rec mat_vec_mul #n m v =
  match m with
  | MNil -> VNil
  | MCons a b c m' ->
    let VCons x v' = v in
    VCons (scalar_add (scalar_mul a x) (vec_dot b v'))
          (vec_add (vec_scalar_mul c x) (mat_vec_mul m' v'))

let rec vec_mat_mul #n r m =
  match m with
  | MNil -> VNil
  | MCons a b c m' ->
    let VCons x r' = r in
    VCons (scalar_add (scalar_mul x a) (vec_dot r' c))
          (vec_add (vec_scalar_mul b x) (vec_mat_mul r' m'))

let rec vec_outer #n c r =
  match c with
  | VNil -> MNil
  | VCons x c' ->
    let VCons y r' = r in
    MCons (scalar_mul x y) (vec_scalar_mul r' x) (vec_scalar_mul c' y) (vec_outer c' r')

let rec mat_add #n m1 m2 =
  match m1 with
  | MNil -> MNil
  | MCons a1 b1 c1 m1' ->
    let MCons a2 b2 c2 m2' = m2 in
    MCons (scalar_add a1 a2) (vec_add b1 b2) (vec_add c1 c2) (mat_add m1' m2')

let rec mat_neg #n m =
  match m with
  | MNil -> MNil
  | MCons a b c m' -> MCons (scalar_neg a) (vec_neg b) (vec_neg c) (mat_neg m')

let rec mat_mul #n m1 m2 =
  match m1 with
  | MNil -> MNil
  | MCons a1 b1 c1 m1' ->
    let MCons a2 b2 c2 m2' = m2 in
    MCons (scalar_add (scalar_mul a1 a2) (vec_dot b1 c2))
          (vec_add (vec_scalar_mul b2 a1) (vec_mat_mul b1 m2'))
          (vec_add (vec_scalar_mul c1 a2) (mat_vec_mul m1' c2))
          (mat_add (vec_outer c1 b2) (mat_mul m1' m2'))

let rec mat_transpose #n m =
  match m with
  | MNil -> MNil
  | MCons a b c m' -> MCons a c b (mat_transpose m')

let mat_vec_mul_cons #n #k a b c m x v = ()
let vec_mat_mul_cons #n #k x r a b c m = ()
let vec_outer_cons #n #k x c y r = ()
let mat_add_cons #n #k a1 b1 c1 m1 a2 b2 c2 m2 = ()
let mat_neg_cons #n #k a b c m = ()
let mat_mul_cons #n #k a1 b1 c1 m1 a2 b2 c2 m2 = ()
let mat_transpose_cons #n #k a b c m = ()

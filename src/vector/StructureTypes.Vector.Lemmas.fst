module StructureTypes.Vector.Lemmas

open StructureTypes.Scalar
open StructureTypes.Scalar.Lemmas
open StructureTypes.Vector

let rec vec_add_inv_r (#n: nat) (v: vec n)
  : Lemma (vec_is_zero (vec_add v (vec_neg v))) [SMTPat (vec_add v (vec_neg v))] =
  match v with
  | VNil -> ()
  | VCons _ v' -> vec_add_inv_r v'

let rec vec_add_inv_l (#n: nat) (v: vec n)
  : Lemma (vec_is_zero (vec_add (vec_neg v) v)) [SMTPat (vec_add (vec_neg v) v)] =
  match v with
  | VNil -> ()
  | VCons _ v' -> vec_add_inv_l v'

let rec vec_add_sub_cancel (#n: nat) (v1 v2: vec n)
  : Lemma (vec_add v2 (vec_add v1 (vec_neg v2)) == v1)
          [SMTPat (vec_add v2 (vec_add v1 (vec_neg v2)))] =
  match v1 with
  | VNil -> ()
  | VCons x v1' ->
    let VCons y v2' = v2 in
    vec_add_sub_cancel v1' v2';
    scalar_add_comm x (scalar_neg y);
    scalar_add_assoc y (scalar_neg y) x

let rec vec_neg_involutive (#n: nat) (v: vec n)
  : Lemma (vec_neg (vec_neg v) == v) [SMTPat (vec_neg (vec_neg v))] =
  match v with
  | VNil -> ()
  | VCons _ v' -> vec_neg_involutive v'

let rec vec_neg_add (#n: nat) (v1 v2: vec n)
  : Lemma (vec_neg (vec_add v1 v2) == vec_add (vec_neg v1) (vec_neg v2))
          [SMTPat (vec_neg (vec_add v1 v2))] =
  match v1 with
  | VNil -> ()
  | VCons _ v1' -> let VCons _ v2' = v2 in vec_neg_add v1' v2'

let rec vec_scalar_mul_neg_r (#n: nat) (v: vec n) (a: num)
  : Lemma (vec_scalar_mul v (scalar_neg a) == vec_neg (vec_scalar_mul v a))
          [SMTPat (vec_scalar_mul v (scalar_neg a))] =
  match v with
  | VNil -> ()
  | VCons _ v' -> vec_scalar_mul_neg_r v' a

let rec vec_scalar_mul_assoc (#n: nat) (v: vec n) (a1 a2: num)
  : Lemma (vec_scalar_mul (vec_scalar_mul v a1) a2 == vec_scalar_mul v (scalar_mul a1 a2)) =
  match v with
  | VNil -> ()
  | VCons x v' -> vec_scalar_mul_assoc v' a1 a2; scalar_mul_assoc x a1 a2

let rec vec_scalar_mul_add_l (#n: nat) (v1 v2: vec n) (a: num)
  : Lemma (vec_scalar_mul (vec_add v1 v2) a == vec_add (vec_scalar_mul v1 a) (vec_scalar_mul v2 a))
          [SMTPat (vec_scalar_mul (vec_add v1 v2) a)] =
  match v1 with
  | VNil -> ()
  | VCons _ v1' -> let VCons _ v2' = v2 in vec_scalar_mul_add_l v1' v2' a

let rec vec_scalar_mul_div_comm (#n: nat) (v: vec n) (a: num) (l: num{scalar_is_nnz l})
  : Lemma (vec_scalar_mul v (scalar_div a l) == vec_scalar_mul (vec_scalar_div v l) a) =
  match v with
  | VNil -> ()
  | VCons x v' -> vec_scalar_mul_div_comm v' a l; scalar_mul_div_comm x a l

let rec vec_scalar_div_assoc (#n: nat) (v: vec n) (a1: num{scalar_is_nnz a1}) (a2: num{scalar_is_nnz a2})
  : Lemma (vec_scalar_div (vec_scalar_div v a1) a2 == vec_scalar_div v (scalar_mul a1 a2))
          [SMTPat (vec_scalar_div (vec_scalar_div v a1) a2)] =
  match v with
  | VNil -> ()
  | VCons _ v' -> vec_scalar_div_assoc v' a1 a2

let rec vec_dot_neg_r (#n: nat) (r: rvec n) (c: cvec n)
  : Lemma (vec_dot r (vec_neg c) == scalar_neg (vec_dot r c))
          [SMTPat (vec_dot r (vec_neg c))] =
  match r with
  | VNil -> ()
  | VCons _ r' -> let VCons _ c' = c in vec_dot_neg_r r' c'

let rec vec_dot_scalar_mul_r (#n: nat) (r: rvec n) (c: cvec n) (a: num)
  : Lemma (vec_dot r (vec_scalar_mul c a) == scalar_mul (vec_dot r c) a)
          [SMTPat (vec_dot r (vec_scalar_mul c a))] =
  match r with
  | VNil -> ()
  | VCons x r' ->
    let VCons y c' = c in
    vec_dot_scalar_mul_r r' c' a;
    scalar_mul_assoc x y a

let rec vec_add_comm (#n: nat) (v1 v2: vec n)
  : Lemma (vec_add v1 v2 == vec_add v2 v1) =
  match v1 with
  | VNil -> ()
  | VCons x v1' -> let VCons y v2' = v2 in vec_add_comm v1' v2'; scalar_add_comm x y

let rec vec_add_assoc (#n: nat) (v1 v2 v3: vec n)
  : Lemma (vec_add (vec_add v1 v2) v3 == vec_add v1 (vec_add v2 v3)) =
  match v1 with
  | VNil -> ()
  | VCons x v1' ->
    let VCons y v2' = v2 in
    let VCons z v3' = v3 in
    vec_add_assoc v1' v2' v3';
    scalar_add_assoc x y z

let rec vec_add_middle_swap (#n: nat) (a b c d: vec n)
  : Lemma (vec_add (vec_add a b) (vec_add c d) == vec_add (vec_add a c) (vec_add b d)) =
  match a with
  | VNil -> ()
  | VCons x a' ->
    let VCons y b' = b in
    let VCons z c' = c in
    let VCons w d' = d in
    vec_add_middle_swap a' b' c' d';
    scalar_add_middle_swap x y z w

let rec vec_scalar_mul_add_r (#n: nat) (v: vec n) (a b: num)
  : Lemma (vec_scalar_mul v (scalar_add a b) == vec_add (vec_scalar_mul v a) (vec_scalar_mul v b)) =
  match v with
  | VNil -> ()
  | VCons x v' -> vec_scalar_mul_add_r v' a b; scalar_mul_add_r x a b

let rec vec_scalar_mul_neg_l (#n: nat) (v: vec n) (a: num)
  : Lemma (vec_scalar_mul (vec_neg v) a == vec_neg (vec_scalar_mul v a)) =
  match v with
  | VNil -> ()
  | VCons x v' -> vec_scalar_mul_neg_l v' a; scalar_mul_neg_l x a

let rec vec_dot_add_r (#n: nat) (r: rvec n) (c1 c2: cvec n)
  : Lemma (vec_dot r (vec_add c1 c2) == scalar_add (vec_dot r c1) (vec_dot r c2)) =
  match r with
  | VNil -> ()
  | VCons x r' ->
    let VCons y1 u1 = c1 in
    let VCons y2 u2 = c2 in
    vec_dot_add_r r' u1 u2;
    scalar_mul_add_r x y1 y2;
    scalar_add_middle_swap (scalar_mul x y1) (scalar_mul x y2) (vec_dot r' u1) (vec_dot r' u2)

let rec vec_dot_add_l (#n: nat) (r1 r2: rvec n) (c: cvec n)
  : Lemma (vec_dot (vec_add r1 r2) c == scalar_add (vec_dot r1 c) (vec_dot r2 c)) =
  match c with
  | VNil -> ()
  | VCons y c' ->
    let VCons x1 r1' = r1 in
    let VCons x2 r2' = r2 in
    vec_dot_add_l r1' r2' c';
    scalar_add_middle_swap (scalar_mul x1 y) (scalar_mul x2 y) (vec_dot r1' c') (vec_dot r2' c')

let rec vec_dot_scalar_mul_l (#n: nat) (r: rvec n) (c: cvec n) (a: num)
  : Lemma (vec_dot (vec_scalar_mul r a) c == scalar_mul (vec_dot r c) a) =
  match r with
  | VNil -> ()
  | VCons x r' ->
    let VCons y c' = c in
    vec_dot_scalar_mul_l r' c' a;
    scalar_mul_swap_r x a y

let rec vec_dot_neg_l (#n: nat) (r: rvec n) (c: cvec n)
  : Lemma (vec_dot (vec_neg r) c == scalar_neg (vec_dot r c)) =
  match r with
  | VNil -> ()
  | VCons x r' ->
    let VCons y c' = c in
    vec_dot_neg_l r' c';
    scalar_mul_neg_l x y

let rec vec_ext (#n: nat) (r1 r2: rvec n)
  : Lemma (requires forall (c: cvec n). vec_dot r1 c == vec_dot r2 c) (ensures r1 == r2) =
  match r1 with
  | VNil -> ()
  | VCons #m x r1' ->
    let VCons y r2' = r2 in
    let e : cvec n = VCons scalar_one (vec_zero #m) in
    assert (vec_dot r1 e == vec_dot r2 e);
    let aux (c': cvec m) : Lemma (vec_dot r1' c' == vec_dot r2' c') =
      let c : cvec n = VCons scalar_zero c' in
      assert (vec_dot r1 c == vec_dot r2 c)
    in
    FStar.Classical.forall_intro aux;
    vec_ext r1' r2'

let rec vec_neg_unique (#n: nat) (v w: vec n)
  : Lemma (requires vec_add v w == vec_zero) (ensures w == vec_neg v) =
  match v with
  | VNil -> ()
  | VCons x v' -> let VCons y w' = w in vec_neg_unique v' w'; scalar_neg_unique x y

let rec vec_scalar_mul_div_cancel (#n: nat) (v: vec n) (a: num{scalar_is_nnz a})
  : Lemma (vec_scalar_div (vec_scalar_mul v a) a == v) =
  match v with
  | VNil -> ()
  | VCons x v' ->
    vec_scalar_mul_div_cancel v' a;
    scalar_mul_cancel_r (scalar_div (scalar_mul x a) a) x a

let rec vec_dot_comm (#n: nat) (u v: vec n) : Lemma (vec_dot u v == vec_dot v u) =
  match u with
  | VNil -> ()
  | VCons x u' -> let VCons y v' = v in vec_dot_comm u' v'; scalar_mul_comm x y

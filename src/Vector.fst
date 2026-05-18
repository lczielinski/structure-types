module Vector

open Scalar

type orient = | Row | Col
let flip (o: orient) : orient = match o with | Row -> Col | Col -> Row

// or: size function computes size of vector. use as a refinement
noeq type vec : orient -> pos -> Type =
  | Vec1 : #o: orient -> num -> vec o 1
  | VecN : #o: orient -> #n: pos -> vec o n -> num -> vec o (n + 1)

let row (#n: pos) (v: vec Row n) : prop = True
let col (#n: pos) (v: vec Col n) : prop = True

let rvec (n: pos) : Type = vec Row n
let cvec (n: pos) : Type = vec Col n

(* zero vector *)
let rec zero_vec (#o: orient) (#n: pos) : vec o n =
  if n = 1 then Vec1 #o zero else VecN (zero_vec #o #(n - 1)) zero

let zero_rvec (#n: pos) : rvec n = zero_vec #Row #n
let zero_cvec (#n: pos) : cvec n = zero_vec #Col #n

let is_zero_vec (#o: orient) (#n: pos) (v: vec o n) : prop = v == zero_vec #o #n

(* add vectors *)
let rec vec_add (#o: orient) (#n: pos) (v1 v2: vec o n) : v3: vec o n 
  {(is_zero_vec v1 ==> v3 == v2) /\ (is_zero_vec v2 ==> v3 == v1)} =
  match v1 with
  | Vec1 x -> let Vec1 y = v2 in Vec1 (scalar_add x y)
  | VecN v1' x -> let VecN v2' y = v2 in VecN (vec_add v1' v2') (scalar_add x y)

(* negate a vector *)
let rec vec_neg (#o: orient) (#n: pos) (v1: vec o n) : v2: vec o n 
  {is_zero_vec v1 ==> is_zero_vec v2} =
  match v1 with
  | Vec1 x -> Vec1 (scalar_neg x)
  | VecN v1' x -> VecN (vec_neg v1') (scalar_neg x)

let rec vec_neg_add_inv_l (#o: orient) (#n: pos) (v: vec o n)
    : Lemma (is_zero_vec (vec_add v (vec_neg v))) [SMTPat (vec_add v (vec_neg v))] =
  match v with
  | Vec1 _ -> ()
  | VecN v' _ -> vec_neg_add_inv_l v'

let rec vec_neg_add_inv_r (#o: orient) (#n: pos) (v: vec o n)
    : Lemma (is_zero_vec (vec_add (vec_neg v) v)) [SMTPat (vec_add (vec_neg v) v)] =
  match v with
  | Vec1 _ -> ()
  | VecN v' _ -> vec_neg_add_inv_r v'

let rec vec_neg_involutive (#o: orient) (#n: pos) (v: vec o n)
    : Lemma (vec_neg (vec_neg v) == v) [SMTPat (vec_neg (vec_neg v))] =
  match v with
  | Vec1 _ -> ()
  | VecN v' _ -> vec_neg_involutive v'

let rec vec_neg_add_dist (#o: orient) (#n: pos) (v1 v2: vec o n)
    : Lemma (vec_neg (vec_add v1 v2) == vec_add (vec_neg v1) (vec_neg v2))
      [SMTPat (vec_neg (vec_add v1 v2))] =
  match v1 with
  | Vec1 _ -> let Vec1 _ = v2 in ()
  | VecN v1' _ -> let VecN v2' _ = v2 in vec_neg_add_dist v1' v2'

(* vector-scalar mul *)
let rec vec_scalar_mul (#o: orient) (#n: pos) (v1: vec o n) (a: num) : v2: vec o n
  {(is_one a ==> v2 == v1) /\ (is_zero_vec v1 ==> is_zero_vec v2) /\ (is_zero a ==> is_zero_vec v2)} =
  match v1 with
  | Vec1 x -> Vec1 (scalar_mul x a)
  | VecN v1' x -> VecN (vec_scalar_mul v1' a) (scalar_mul x a)

let rec vec_scalar_mul_neg (#o: orient) (#n: pos) (v: vec o n) (a: num)
    : Lemma (vec_scalar_mul v (scalar_neg a) == vec_neg (vec_scalar_mul v a))
      [SMTPat (vec_scalar_mul v (scalar_neg a))] =
  match v with
  | Vec1 _ -> ()
  | VecN v' _ -> vec_scalar_mul_neg v' a

let rec vec_scalar_mul_assoc (#o: orient) (#n: pos) (v: vec o n) (a1 a2: num)
    : Lemma (vec_scalar_mul (vec_scalar_mul v a1) a2 == vec_scalar_mul v (scalar_mul a1 a2)) =
      // [SMTPat (vec_scalar_mul (vec_scalar_mul v a1) a2)] =
  match v with
  | Vec1 a -> scalar_mul_assoc a a1 a2
  | VecN v' x ->
    vec_scalar_mul_assoc v' a1 a2;
    scalar_mul_assoc x a1 a2

let rec vec_scalar_mul_add_dist (#o: orient) (#n: pos) (v1 v2: vec o n) (a: num)
    : Lemma (vec_scalar_mul (vec_add v1 v2) a == vec_add (vec_scalar_mul v1 a) (vec_scalar_mul v2 a))
      [SMTPat (vec_scalar_mul (vec_add v1 v2) a)] =
  match v1 with
  | Vec1 _ -> let Vec1 _ = v2 in ()
  | VecN v1' _ -> let VecN v2' _ = v2 in vec_scalar_mul_add_dist v1' v2' a

(* vector-scalar div *)
let rec vec_scalar_div (#o: orient) (#n: pos) (v1: vec o n) (a: num{is_nnz a}) : v2: vec o n 
  {vec_scalar_mul v2 a == v1} =
  match v1 with
  | Vec1 x -> Vec1 (scalar_div x a)
  | VecN v1' x -> VecN (vec_scalar_div v1' a) (scalar_div x a)

let rec vec_scalar_div_assoc (#o: orient) (#n: pos) (v: vec o n)
      (a1: num{is_nnz a1}) (a2: num{is_nnz a2})
    : Lemma (vec_scalar_div (vec_scalar_div v a1) a2 == vec_scalar_div v (scalar_mul a1 a2))
      [SMTPat (vec_scalar_div (vec_scalar_div v a1) a2)] =
  match v with
  | Vec1 _ -> ()
  | VecN v' _ -> vec_scalar_div_assoc v' a1 a2

(* inner product *)
let rec inner_prod (#n: pos) (r: rvec n) (c: cvec n) : a: num 
  {(is_zero_vec r \/ is_zero_vec c) ==> is_zero a} =
  match r with
  | Vec1 x -> let Vec1 y = c in scalar_mul x y
  | VecN r' x -> let VecN c' y = c in scalar_add (inner_prod r' c') (scalar_mul x y)

let rec inner_prod_neg_r (#n: pos) (r: rvec n) (c: cvec n)
    : Lemma (inner_prod r (vec_neg c) == scalar_neg (inner_prod r c))
      [SMTPat (inner_prod r (vec_neg c))] =
  match r with
  | Vec1 _ -> let Vec1 _ = c in ()
  | VecN r' _ -> let VecN c' _ = c in inner_prod_neg_r r' c'

let rec inner_prod_scalar_r (#n: pos) (r: rvec n) (c: cvec n) (a: num)
    : Lemma (inner_prod r (vec_scalar_mul c a) == scalar_mul (inner_prod r c) a)
      [SMTPat (inner_prod r (vec_scalar_mul c a))] =
  match r with
  | Vec1 x ->
    let Vec1 y = c in
    scalar_mul_assoc x y a
  | VecN r' rx ->
    let VecN c' cy = c in
    inner_prod_scalar_r r' c' a;
    scalar_mul_assoc rx cy a

(* transpose vector *)
let rec vec_trans (#o: orient) (#n: pos) (v1: vec o n) : v2: vec (flip o) n 
  {is_zero_vec v1 ==> is_zero_vec v2} =
  match v1 with
  | Vec1 x -> Vec1 x
  | VecN v1' x -> VecN (vec_trans v1') x

let rec vec_trans_scalar_div (#o: orient) (#n: pos) (v: vec o n) (a: num{is_nnz a})
    : Lemma (vec_trans (vec_scalar_div v a) == vec_scalar_div (vec_trans v) a)
      [SMTPat (vec_trans (vec_scalar_div v a))] =
  match v with
  | Vec1 _ -> ()
  | VecN v' _ -> vec_trans_scalar_div v' a
  
let rec vec_trans_involutive (#o: orient) (#n: pos) (v: vec o n)
    : Lemma (vec_trans (vec_trans v) == v) [SMTPat (vec_trans (vec_trans v))] =
  match v with
  | Vec1 _ -> ()
  | VecN v' _ -> vec_trans_involutive v'

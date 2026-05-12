module Vector

open Scalar

type orient = | Row | Col

let flip (o: orient) : orient = match o with | Row -> Col | Col -> Row

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

let zero_rvec (n: pos) : rvec n = zero_vec #Row #n
let zero_cvec (n: pos) : cvec n = zero_vec #Col #n

let is_zero_vec (#o: orient) (#n: pos) (v: vec o n) : prop = v == zero_vec #o #n

(* add vectors *)
let rec vec_add (#o: orient) (#n: pos) (v1 v2: vec o n) : vec o n =
  match v1 with
  | Vec1 x -> let Vec1 y = v2 in Vec1 (scalar_add x y)
  | VecN v1' x -> let VecN v2' y = v2 in VecN (vec_add v1' v2') (scalar_add x y)

let rec vec_add_zero_l (#o: orient) (#n: pos) (v1 v2: vec o n)
    : Lemma (requires is_zero_vec v1) (ensures vec_add v1 v2 == v2) [SMTPat (vec_add v1 v2)] =
  match v1 with 
  | Vec1 _ -> let Vec1 _ = v2 in ()
  | VecN v1' _ -> let VecN v2' _ = v2 in vec_add_zero_l v1' v2'

let rec vec_add_zero_r (#o: orient) (#n: pos) (v1 v2: vec o n)
    : Lemma (requires is_zero_vec v2) (ensures vec_add v1 v2 == v1) [SMTPat (vec_add v1 v2)] =
  match v2 with
  | Vec1 _ -> let Vec1 _ = v1 in ()
  | VecN v2' _ -> let VecN v1' _ = v1 in vec_add_zero_r v1' v2'

(* negate a vector *)
let rec vec_neg (#o: orient) (#n: pos) (v: vec o n) : vec o n =
  match v with
  | Vec1 x -> Vec1 (scalar_neg x)
  | VecN v' x -> VecN (vec_neg v') (scalar_neg x)

let rec vec_neg_zero (#o: orient) (#n: pos) (v: vec o n)
    : Lemma (requires is_zero_vec v) (ensures is_zero_vec (vec_neg v)) [SMTPat (vec_neg v)] =
  match v with
  | Vec1 _ -> ()
  | VecN v' _ -> vec_neg_zero v'

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

(* vector-scalar mul *)
let rec vec_scalar_mul (#o: orient) (#n: pos) (v: vec o n) (a: num) : vec o n =
  match v with
  | Vec1 x -> Vec1 (scalar_mul x a)
  | VecN v' x -> VecN (vec_scalar_mul v' a) (scalar_mul x a)

let rec vec_scalar_mul_one (#o: orient) (#n: pos) (v: vec o n) (a: num)
    : Lemma (requires is_one a) (ensures vec_scalar_mul v a == v) [SMTPat (vec_scalar_mul v a)] =
  match v with
  | Vec1 _ -> ()
  | VecN v' _ -> vec_scalar_mul_one v' a

let rec vec_scalar_mul_zero (#o: orient) (#n: pos) (v: vec o n) (a: num)
    : Lemma (requires is_zero_vec v)
      (ensures is_zero_vec (vec_scalar_mul v a))
      [SMTPat (vec_scalar_mul v a)] =
  match v with
  | Vec1 _ -> ()
  | VecN v' _ -> vec_scalar_mul_zero v' a

(* vector-scalar div *)
let rec vec_scalar_div (#o: orient) (#n: pos) (v: vec o n) (a: num{is_nnz a}) : vec o n =
  match v with
  | Vec1 x -> Vec1 (scalar_div x a)
  | VecN v' x -> VecN (vec_scalar_div v' a) (scalar_div x a)

let rec vec_scalar_div_assoc (#o: orient) (#n: pos) (v: vec o n)
      (a1: num{is_nnz a1}) (a2: num{is_nnz a2})
    : Lemma (vec_scalar_div (vec_scalar_div v a1) a2 == vec_scalar_div v (scalar_mul a1 a2))
      [SMTPat (vec_scalar_div (vec_scalar_div v a1) a2)] =
  match v with
  | Vec1 _ -> ()
  | VecN v' _ -> vec_scalar_div_assoc v' a1 a2

(* inner product *)
let rec inner_prod (#n: pos) (r: rvec n) (c: cvec n) : num =
  match r with
  | Vec1 x -> let Vec1 y = c in scalar_mul x y
  | VecN r' rx -> let VecN c' cy = c in scalar_add (inner_prod r' c') (scalar_mul rx cy)

let rec inner_prod_zero (#n: pos) (r: rvec n) (c: cvec n)
    : Lemma (requires is_zero_vec r \/ is_zero_vec c) (ensures is_zero (inner_prod r c))
      [SMTPat (inner_prod r c)] =
  match r with
  | Vec1 _ -> let Vec1 _ = c in ()
  | VecN r' _ -> let VecN c' _ = c in inner_prod_zero r' c'

(* transpose vector *)
let rec vec_trans (#o: orient) (#n: pos) (v: vec o n) : vec (flip o) n =
  match v with
  | Vec1 x -> Vec1 x
  | VecN v' x -> VecN (vec_trans v') x

let rec vec_trans_zero (#o: orient) (#n: pos) (v: vec o n)
    : Lemma (requires is_zero_vec v) (ensures is_zero_vec (vec_trans v)) [SMTPat (vec_trans v)] =
  match v with
  | Vec1 _ -> ()
  | VecN v' _ -> vec_trans_zero v'

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

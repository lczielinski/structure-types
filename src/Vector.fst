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
assume val vec_add (#o: orient) (#n: pos) (v1 v2: vec o n) : v3: vec o n {
  (is_zero_vec v1 ==> v3 == v2) /\
  (is_zero_vec v2 ==> v3 == v1)
}

(* negate a vector *)
assume val neg (#o: orient) (#n: pos) (v1: vec o n) : vec o n 

assume val neg_zero : #n:pos -> #o:orient -> v:vec o n ->
  Lemma (requires is_zero_vec v) (ensures is_zero_vec (neg v)) [SMTPat (neg v)]

assume val neg_add_inv_l : #n:pos -> #o:orient -> v:vec o n ->
  Lemma (is_zero_vec (vec_add v (neg v))) [SMTPat (vec_add v (neg v))]

assume val neg_add_inv_r : #n:pos -> #o:orient -> v:vec o n ->
  Lemma (is_zero_vec (vec_add (neg v) v)) [SMTPat (vec_add (neg v) v)]

assume val neg_involutive : #n:pos -> #o:orient -> v:vec o n ->
  Lemma (neg (neg v) == v) [SMTPat (neg (neg v))]

(* vector-scalar mult *)
assume val vec_scalar_mul : #n:pos -> #o:orient -> v1:vec o n -> a:num -> v2:vec o n

assume val vec_scalar_mul_zero : #n:pos -> #o:orient -> v:vec o n -> a:num ->
  Lemma (requires is_zero_vec v) (ensures is_zero_vec (vec_scalar_mul v a)) 
  [SMTPat (vec_scalar_mul v a)]

assume val vec_scalar_mul_one : #n:pos -> #o:orient -> v:vec o n -> a:num ->
  Lemma (requires is_one a) (ensures vec_scalar_mul v a == v) 
  [SMTPat (vec_scalar_mul v a)]

assume val vec_scalar_div : #n:pos -> #o:orient -> v1:vec o n -> a:num{is_nnz a} -> v2:vec o n{
  vec_scalar_mul v2 a == v1
}

assume val vec_scalar_div_assoc : #n:pos -> #o:orient -> v:vec o n -> a1:num{is_nnz a1} -> a2:num{is_nnz a2} ->
  Lemma (vec_scalar_div (vec_scalar_div v a1) a2 == vec_scalar_div v (scalar_mul a1 a2))
        [SMTPat (vec_scalar_div (vec_scalar_div v a1) a2)]

(* inner product *)
assume val inner_prod : #n:pos -> rvec n -> cvec n -> num

assume val inner_prod_zero : #n:pos -> r:rvec n -> c:cvec n ->
  Lemma (requires is_zero_vec r \/ is_zero_vec c) (ensures is_zero (inner_prod r c)) 
  [SMTPat (inner_prod r c)]

(* transpose vector *)
assume val trans_vec : #n:pos -> #o:orient -> v1:vec o n -> v2:vec (flip o) n{
  (is_zero_vec v1 ==> is_zero_vec v2)
}

assume val trans_vec_scalar_div : #n:pos -> #o:orient -> v:vec o n -> a:num{is_nnz a} ->
  Lemma (trans_vec (vec_scalar_div v a) == vec_scalar_div (trans_vec v) a)
        [SMTPat (trans_vec (vec_scalar_div v a))]

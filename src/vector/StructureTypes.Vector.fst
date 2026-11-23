module StructureTypes.Vector

open StructureTypes.Scalar

noeq type vec : nat -> Type =
  | VNil : vec 0
  | VCons : #n: nat -> num -> vec n -> vec (n + 1)

let rvec (n: nat) : Type = vec n
let cvec (n: nat) : Type = vec n

let rec vec_zero (#n: nat) : vec n =
  if n = 0 then VNil else VCons scalar_zero (vec_zero #(n - 1))

let vec_is_zero (#n: nat) (v: vec n) : prop = v == vec_zero #n

let rec vec_add (#n: nat) (v1 v2: vec n) : v3: vec n
  {(vec_is_zero v1 ==> v3 == v2) /\ (vec_is_zero v2 ==> v3 == v1)} =
  match v1 with
  | VNil -> VNil
  | VCons x v1' -> let VCons y v2' = v2 in VCons (scalar_add x y) (vec_add v1' v2')

let rec vec_neg (#n: nat) (v1: vec n) : v2: vec n {vec_is_zero v1 ==> vec_is_zero v2} =
  match v1 with
  | VNil -> VNil
  | VCons x v1' -> VCons (scalar_neg x) (vec_neg v1')

let vec_sub (#n: nat) (v1 v2: vec n) : vec n =
  vec_add v1 (vec_neg v2)

let rec vec_scalar_mul (#n: nat) (v1: vec n) (a: num) : v2: vec n
  {(scalar_is_one a ==> v2 == v1) /\ (vec_is_zero v1 ==> vec_is_zero v2) /\ (scalar_is_zero a ==> vec_is_zero v2)} =
  match v1 with
  | VNil -> VNil
  | VCons x v1' -> VCons (scalar_mul x a) (vec_scalar_mul v1' a)

let rec vec_scalar_div (#n: nat) (v1: vec n) (a: num{scalar_is_nnz a}) : v2: vec n
  {vec_scalar_mul v2 a == v1} =
  match v1 with
  | VNil -> VNil
  | VCons x v1' -> VCons (scalar_div x a) (vec_scalar_div v1' a)

let rec vec_dot (#n: nat) (r: rvec n) (c: cvec n) : a: num
  {(vec_is_zero r \/ vec_is_zero c) ==> scalar_is_zero a} =
  match r with
  | VNil -> scalar_zero
  | VCons x r' -> let VCons y c' = c in scalar_add (scalar_mul x y) (vec_dot r' c')

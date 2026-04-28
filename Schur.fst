module Schur

open Scalar
open Vector
open MatrixType
open Matrix

let schur1 (#n:pos) (d:mat n) (c:cvec n) (a:num{nnz a}) (b:rvec n) : mat n =
  mat_sub d (outer_prod (vec_scalar_div c a) b)

assume val schur1_spd : #n:pos ->
  d:mat n -> c:cvec n -> a:num{posr a} -> b:rvec n ->
  Lemma (requires spd (augment #(n+1) d c a b))
        (ensures spd (schur1 d c a b))
  [SMTPat (spd (schur1 d c a b))]

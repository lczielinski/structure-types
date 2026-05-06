module Solve

open Scalar
open Vector
open MatrixType
open Matrix
open MatMul
open OneByOne
open TriInv

let solve (#n:pos) (l:mat n{unit_lower l}) (b:cvec n) : 
    x:cvec n{mat_vec_mul l x == b} =
    let l_inv = triangular_inv l in
    mat_vec_mul l_inv b

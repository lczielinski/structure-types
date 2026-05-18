module OneByOne

open Scalar
open Vector
open MatrixType
open Matrix
open MatMul

assume val one_by_one_is_identity : m:mat 1 ->
  Lemma (requires unit_diag m) (ensures is_id m)
        [SMTPat (unit_diag (m <: mat 1))]

assume val one_by_one_lower : m:mat 1 -> Lemma (lower m) [SMTPat (lower m)]
assume val one_by_one_upper : m:mat 1 -> Lemma (upper m) [SMTPat (upper m)]
assume val one_by_one_sym : m:mat 1 -> Lemma (symmetric m) [SMTPat (symmetric m)]

assume val extract_transpose : m:mat 1 ->
  Lemma (ensures transpose m == m)
        [SMTPat (transpose m)]

assume val inv_1x1_nnz_diag : m:mat 1 ->
  Lemma (requires inv m) (ensures nnz_diag m) [SMTPat (inv (m <: mat 1))]

assume val mul_1x1 : m1:mat 1 -> m2:mat 1 ->
  Lemma (let Mat1 a1 = m1 in let Mat1 a2 = m2 in mat_mul m1 m2 == Mat1 (scalar_mul a1 a2))
  [SMTPat (mat_mul m1 m2)]

assume val spd_mat1_pos : a:num ->
  Lemma (requires spd (Mat1 a)) (ensures is_pos a) [SMTPat (spd (Mat1 a))]
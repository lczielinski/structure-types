module OneByOne

open Scalar
open Vector
open MatrixType
open Matrix
open MatMul

assume val one_by_one_is_identity : m:mat 1 ->
  Lemma (requires unit_diag m) (ensures identity m)
        [SMTPat (unit_diag (m <: mat 1))]

assume val one_by_one_lower : m:mat 1 -> Lemma (lower m) [SMTPat (lower m)]
assume val one_by_one_upper : m:mat 1 -> Lemma (upper m) [SMTPat (upper m)]
assume val one_by_one_sym : m:mat 1 -> Lemma (symmetric m) [SMTPat (symmetric m)]

assume val extract : m:mat 1 -> a:num{
  (pos_diag m ==> posr a) /\
  (nnz_diag m ==> nnz a)
}

assume val build_mat : a:num -> m:mat 1{
  (posr a ==> pos_diag m) /\
  (nnz a ==> nnz_diag m)
}

assume val extract_transpose : m:mat 1 ->
  Lemma (ensures extract (transpose m) == extract m)
        [SMTPat (extract (transpose m))]

assume val extract_build : a:num ->
  Lemma (ensures extract (build_mat a) == a) [SMTPat (extract (build_mat a))]

assume val one_by_one_equal : m1:mat 1 -> m2:mat 1 ->
  Lemma (requires extract m1 == extract m2) (ensures m1 == m2)
        [SMTPat (extract m1); SMTPat (extract m2)]

assume val extract_mul : m1:mat 1 -> m2:mat 1 ->
  Lemma (ensures extract (mat_mul m1 m2) == scalar_mul (extract m1) (extract m2))
        [SMTPat (mat_mul m1 m2)]

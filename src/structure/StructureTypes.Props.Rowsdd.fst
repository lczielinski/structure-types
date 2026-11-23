module StructureTypes.Props.Rowsdd

open StructureTypes.Scalar
open StructureTypes.Vector
open StructureTypes.Matrix
open StructureTypes.Shape

assume val rowsdd: #n: nat -> mat n -> prop

assume val rowsdd_nnz_diag (#n: nat) (m: mat n)
  : Lemma (requires rowsdd m) (ensures nnz_diag m) [SMTPat (rowsdd m); SMTPat (nnz_diag m)]

assume val rowsdd_augment (#n: nat) (#k: pos{k == n + 1}) (a: num) (b: rvec n) (c: cvec n) (m: mat n)
  : Lemma (requires rowsdd #k (MCons a b c m)) (ensures is_nnz a /\ rowsdd m)
          [SMTPat (rowsdd #k (MCons a b c m))]

assume val schur1_rowsdd (#n: pos) (#k: nat{k == n - 1}) (m: mat n)
  : Lemma (requires rowsdd m) (ensures rowsdd #k (schur1 m)) [SMTPat (rowsdd #k (schur1 m))]

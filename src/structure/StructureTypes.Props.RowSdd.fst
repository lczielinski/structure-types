module StructureTypes.Props.RowSdd

open StructureTypes.Scalar
open StructureTypes.Vector
open StructureTypes.Matrix
open StructureTypes.Shape

assume val row_sdd: #n: nat -> mat n -> prop

assume val row_sdd_nnz_diag (#n: nat) (m: mat n)
  : Lemma (requires row_sdd m) (ensures nnz_diag m) [SMTPat (row_sdd m); SMTPat (nnz_diag m)]

assume val row_sdd_cons (#n: nat) (#k: pos{k == n + 1}) (a: num) (b: rvec n) (c: cvec n) (m: mat n)
  : Lemma (requires row_sdd #k (MCons a b c m)) (ensures scalar_is_nnz a /\ row_sdd m)
          [SMTPat (row_sdd #k (MCons a b c m))]

assume val row_sdd_mat_schur (#n: pos) (#k: nat{k == n - 1}) (m: mat n)
  : Lemma (requires row_sdd m) (ensures row_sdd #k (mat_schur m)) [SMTPat (row_sdd #k (mat_schur m))]

module StructureTypes.Props.Invertible

open StructureTypes.Matrix

assume val invertible: #n: nat -> mat n -> prop

assume val invertible_mat_schur (#n: pos) (#k: nat{k == n - 1}) (m: mat n)
  : Lemma (requires invertible m /\ top_left_nnz m) (ensures invertible #k (mat_schur m)) [SMTPat (invertible #k (mat_schur m))]

module StructureTypes.Props.Invertible

open StructureTypes.Matrix

val invertible (#n: nat) (m: mat n) : prop

val invertible_intro (#n: nat) (m r: mat n)
  : Lemma (requires mat_is_inverse m r) (ensures invertible m)

val invertible_mat_schur (#n: pos) (#k: nat{k == n - 1}) (m: mat n)
  : Lemma (requires invertible m /\ top_left_nnz m) (ensures invertible #k (mat_schur m))
          [SMTPat (invertible #k (mat_schur m))]

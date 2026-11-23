module StructureTypes.Props.Inv

open StructureTypes.Matrix

assume val inv: #n: nat -> mat n -> prop

assume val schur1_inv (#n: pos) (#k: nat{k == n - 1}) (m: mat n)
  : Lemma (requires inv m /\ top_left_nnz m) (ensures inv #k (schur1 m)) [SMTPat (inv #k (schur1 m))]

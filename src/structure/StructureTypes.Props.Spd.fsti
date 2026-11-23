module StructureTypes.Props.Spd

open StructureTypes.Scalar
open StructureTypes.Vector
open StructureTypes.Matrix
open StructureTypes.Shape

val spd (#n: nat) (m: mat n) : prop

val spd_symmetric (#n: nat) (m: mat n)
  : Lemma (requires spd m) (ensures symmetric m) [SMTPat (spd m)]

val spd_cons (#n: nat) (#k: pos{k == n + 1}) (a: num) (b: rvec n) (c: cvec n) (m: mat n)
  : Lemma (requires spd #k (MCons a b c m)) (ensures scalar_is_pos a /\ spd m)
          [SMTPat (spd #k (MCons a b c m))]

val spd_pos_diag (#n: nat) (m: mat n)
  : Lemma (requires spd m) (ensures pos_diag m) [SMTPat (spd m); SMTPat (pos_diag m)]

val spd_mat_schur (#n: pos) (#k: nat{k == n - 1}) (m: mat n)
  : Lemma (requires spd m /\ top_left_nnz m) (ensures spd #k (mat_schur m)) [SMTPat (spd #k (mat_schur m))]

module StructureTypes.Props.Spd

open StructureTypes.Scalar
open StructureTypes.Vector
open StructureTypes.Matrix
open StructureTypes.Shape

assume val spd: #n: nat -> mat n -> prop

assume val spd_symmetric (#n: nat) (m: mat n)
  : Lemma (requires spd m) (ensures symmetric m) [SMTPat (spd m)]

assume val spd_pos_diag (#n: nat) (m: mat n)
  : Lemma (requires spd m) (ensures pos_diag m) [SMTPat (spd m); SMTPat (pos_diag m)]

assume val spd_augment (#n: nat) (#k: pos{k == n + 1}) (a: num) (b: rvec n) (c: cvec n) (m: mat n)
  : Lemma (requires spd #k (MCons a b c m)) (ensures is_pos a /\ spd m)
          [SMTPat (spd #k (MCons a b c m))]

assume val schur1_spd (#n: pos) (#k: nat{k == n - 1}) (m: mat n)
  : Lemma (requires spd m) (ensures spd #k (schur1 m)) [SMTPat (spd #k (schur1 m))]

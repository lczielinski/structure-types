module StructureTypes.Props.Perm

open StructureTypes.Scalar
open StructureTypes.Vector
open StructureTypes.Matrix
open StructureTypes.Props.Inv

assume val perm: #n: nat -> mat n -> prop

assume val perm_is_inv (#n: nat) (m: mat n)
  : Lemma (requires perm m) (ensures inv m) [SMTPat (inv m)]

assume val id_mat_is_perm (#n: nat) : Lemma (perm (id_mat #n)) [SMTPat (perm (id_mat #n))]

assume val perm_augment (#n: nat) (#k: pos{k == n + 1}) (m: mat n)
  : Lemma (requires perm m) (ensures perm #k (MCons one zero_vec zero_vec m))
          [SMTPat (perm #k (MCons one zero_vec zero_vec m))]

assume val mat_mul_perm (#n: nat) (m1 m2: mat n)
  : Lemma (requires perm m1 /\ perm m2) (ensures perm (mat_mul m1 m2))
          [SMTPat (perm (mat_mul m1 m2))]

assume val transpose_perm (#n: nat) (m: mat n)
  : Lemma (requires perm m) (ensures perm (transpose m)) [SMTPat (perm (transpose m))]

assume val perm_transpose_inverse (#n: nat) (m: mat n)
  : Lemma (requires perm m) (ensures is_inverse m (transpose m))
          [SMTPatOr [[SMTPat (mat_mul m (transpose m))]; [SMTPat (mat_mul (transpose m) m)]]]

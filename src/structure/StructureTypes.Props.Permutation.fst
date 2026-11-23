module StructureTypes.Props.Permutation

open StructureTypes.Scalar
open StructureTypes.Vector
open StructureTypes.Matrix
open StructureTypes.Props.Invertible

assume val permutation: #n: nat -> mat n -> prop

assume val permutation_mat_id (#n: nat) : Lemma (permutation (mat_id #n)) [SMTPat (permutation (mat_id #n))]

assume val permutation_cons (#n: nat) (#k: pos{k == n + 1}) (m: mat n)
  : Lemma (requires permutation m) (ensures permutation #k (MCons scalar_one vec_zero vec_zero m))
          [SMTPat (permutation #k (MCons scalar_one vec_zero vec_zero m))]

assume val permutation_mat_mul (#n: nat) (m1 m2: mat n)
  : Lemma (requires permutation m1 /\ permutation m2) (ensures permutation (mat_mul m1 m2))
          [SMTPat (permutation (mat_mul m1 m2))]

assume val permutation_mat_transpose (#n: nat) (m: mat n)
  : Lemma (requires permutation m) (ensures permutation (mat_transpose m)) [SMTPat (permutation (mat_transpose m))]

assume val permutation_inverse_transpose (#n: nat) (m: mat n)
  : Lemma (requires permutation m) (ensures mat_is_inverse m (mat_transpose m))
          [SMTPatOr [[SMTPat (mat_mul m (mat_transpose m))]; [SMTPat (mat_mul (mat_transpose m) m)]]]

let permutation_invertible (#n: nat) (m: mat n)
  : Lemma (requires permutation m) (ensures invertible m) [SMTPat (invertible m)] =
  permutation_inverse_transpose m;
  invertible_intro m (mat_transpose m)

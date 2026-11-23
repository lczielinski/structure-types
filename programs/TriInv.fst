module TriInv

open StructureTypes.All

(* triangular inverse function *)
let rec tri_inv (#n:nat) (l:mat n{unit_lower l}) :
  r:mat n{unit_lower r /\ mat_is_inverse l r} =
  match l with
  | MNil -> MNil
  | MCons _ _ c l' ->
    let l'_inv = tri_inv l' in
    let c' = vec_neg (mat_vec_mul l'_inv c) in
    MCons scalar_one vec_zero c' l'_inv

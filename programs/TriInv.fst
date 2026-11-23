module TriInv

open StructureTypes.All

(* triangular inverse function *)
let rec triangular_inv (#n:nat) (l:mat n{unit_lower l}) :
  r:mat n{unit_lower r /\ is_inverse l r} =
  match l with
  | MNil -> MNil
  | MCons _ _ c l' ->
    let l'_inv = triangular_inv l' in
    let c' = vec_neg (mat_vec_mul l'_inv c) in
    MCons one zero_vec c' l'_inv

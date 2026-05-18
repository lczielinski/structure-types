module TriInv

open All

(* triangular inverse function *)
let rec triangular_inv (#n:pos) (l:mat n{unit_lower l}) :
  r:mat n{unit_lower r /\ is_inverse l r} =
  match l with 
  | Mat1 _ -> l 
  | MatN l' c a b ->
    let l'_inv = triangular_inv l' in
    let b' = vec_neg (mat_vec_mul l'_inv c) in
    MatN l'_inv b' one zero_rvec 
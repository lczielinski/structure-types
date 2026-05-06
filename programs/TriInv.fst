module TriInv

open All

(* triangular inverse function *)
#push-options "--split_queries always"
let rec triangular_inv (#n:pos) (l:mat n{unit_lower l}) :
  r:mat n{unit_lower r /\ is_inverse l r} =
  match n with
  | 1 -> l
  | _ ->
    let (|c, _, _, l'|) = destruct #n l in
    let l'_inv = triangular_inv l' in
    let b = neg (mat_vec_mul l'_inv c) in
    augment l'_inv b _one _zero_rvec
#pop-options
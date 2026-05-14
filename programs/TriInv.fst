module TriInv

open All

(* triangular inverse function *)
#push-options "--split_queries always"
let rec triangular_inv (#n:pos) (l:mat n{unit_lower l}) :
  r:mat n{unit_lower r /\ is_inverse l r} =
  match l with
  | Mat1 a -> l
  | MatN l' c corner row ->
    let l'_inv = triangular_inv l' in
    let b = vec_neg (mat_vec_mul l'_inv c) in
    let r = MatN l'_inv b one zero_rvec in

    let tl_lr : mat (n - 1) =
      mat_add (outer_prod c (zero_rvec)) (mat_mul l' l'_inv) in
    r
#pop-options
module TriInv

open All

(* triangular inverse function *)
#push-options "--split_queries always"
let rec triangular_inv (#n:pos) (l:mat n{unit_lower l}) :
  r:mat n{unit_lower r /\ is_inverse l r} =
  match l with 
  | Mat1 _ -> l 
  | MatN l' c a b ->
  // match n with
  // | 1 -> l
  // | _ ->
  //   let (|c, _, _, l'|) = destruct #n l in
    // assert (lower l');
    let l'_inv = triangular_inv l' in
    // assert (lower l'_inv);
    let b' = vec_neg (mat_vec_mul l'_inv c) in
    let r = MatN l'_inv b' one zero_rvec in
    // assert (unit_lower r);
    // assert (mat_mul l r == MatN (mat_add (outer_prod c zero_rvec) (mat_mul l' l'_inv))
    //                      (vec_add (vec_scalar_mul c one) (mat_vec_mul l' b'))
    //                      (scalar_add (scalar_mul a one) (inner_prod b b'))
    //                      (vec_add (vec_scalar_mul zero_rvec a) (vec_mat_mul b l'_inv)));
    // assert (mat_add (outer_prod c zero_rvec) (mat_mul l' l'_inv) == _id_mat);
    
    r
#pop-options
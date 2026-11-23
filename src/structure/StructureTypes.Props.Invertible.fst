module StructureTypes.Props.Invertible

open StructureTypes.Matrix
open StructureTypes.Matrix.Lemmas

let invertible #n m = exists (r: mat n). mat_is_inverse m r

let invertible_intro #n m r =
  FStar.Classical.exists_intro (fun (r': mat n) -> mat_is_inverse m r') r

let invertible_mat_schur #n #k m =
  let MCons #j a b c d = m in
  let aux (r: mat n)
    : Lemma (requires mat_is_inverse m r) (ensures invertible #k (mat_schur m)) =
    let MCons alpha beta gamma delta = r in
    mat_schur_inverse #j #n a b c d alpha beta gamma delta;
    invertible_intro (mat_schur m) delta
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

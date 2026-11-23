module StructureTypes.Shape

open StructureTypes.Scalar
open StructureTypes.Vector
open StructureTypes.Matrix

let rec lower (#n: nat) (m: mat n) : prop =
  match m with
  | MNil -> True
  | MCons _ b _ m' -> vec_is_zero b /\ lower m'

let rec upper (#n: nat) (m: mat n) : prop =
  match m with
  | MNil -> True
  | MCons _ _ c m' -> vec_is_zero c /\ upper m'

let diagonal (#n: nat) (m: mat n) : prop = lower m /\ upper m

let rec unit_diag (#n: nat) (m: mat n) : prop =
  match m with
  | MNil -> True
  | MCons a _ _ m' -> scalar_is_one a /\ unit_diag m'

let rec pos_diag (#n: nat) (m: mat n) : prop =
  match m with
  | MNil -> True
  | MCons a _ _ m' -> scalar_is_pos a /\ pos_diag m'

let rec nnz_diag (#n: nat) (m: mat n) : prop =
  match m with
  | MNil -> True
  | MCons a _ _ m' -> scalar_is_nnz a /\ nnz_diag m'

let unit_lower (#n: nat) (m: mat n) : prop = lower m /\ unit_diag m

let symmetric (#n: nat) (m: mat n) : prop = m == mat_transpose m

let triangular_compat (#n: nat) (m1 m2: mat n) : prop =
  (lower m1 /\ lower m2) \/ (upper m1 /\ upper m2)

let rec unit_diag_pos_diag (#n: nat) (m: mat n)
  : Lemma (requires unit_diag m) (ensures pos_diag m) [SMTPat (pos_diag m)] =
  match m with
  | MNil -> ()
  | MCons _ _ _ m' -> unit_diag_pos_diag m'

let rec pos_diag_nnz_diag (#n: nat) (m: mat n)
  : Lemma (requires pos_diag m) (ensures nnz_diag m) [SMTPat (nnz_diag m)] =
  match m with
  | MNil -> ()
  | MCons _ _ _ m' -> pos_diag_nnz_diag m'

let nnz_diag_top_left_nnz (#n: pos) (m: mat n)
  : Lemma (requires nnz_diag m) (ensures top_left_nnz m) [SMTPat (top_left_nnz m)] = ()

let rec lower_mat_id (#n: nat) : Lemma (lower (mat_id #n)) [SMTPat (lower (mat_id #n))] =
  if n = 0 then () else lower_mat_id #(n - 1)

let rec upper_mat_id (#n: nat) : Lemma (upper (mat_id #n)) [SMTPat (upper (mat_id #n))] =
  if n = 0 then () else upper_mat_id #(n - 1)

let rec unit_diag_mat_id (#n: nat) : Lemma (unit_diag (mat_id #n)) [SMTPat (unit_diag (mat_id #n))] =
  if n = 0 then () else unit_diag_mat_id #(n - 1)

let rec lower_mat_mul (#n: nat) (m1 m2: mat n)
  : Lemma (requires lower m1 /\ lower m2) (ensures lower (mat_mul m1 m2))
          [SMTPat (lower (mat_mul m1 m2))] =
  match m1 with
  | MNil -> ()
  | MCons _ _ _ m1' -> let MCons _ _ _ m2' = m2 in lower_mat_mul m1' m2'

let rec upper_mat_mul (#n: nat) (m1 m2: mat n)
  : Lemma (requires upper m1 /\ upper m2) (ensures upper (mat_mul m1 m2))
          [SMTPat (upper (mat_mul m1 m2))] =
  match m1 with
  | MNil -> ()
  | MCons _ _ _ m1' -> let MCons _ _ _ m2' = m2 in upper_mat_mul m1' m2'

let rec unit_diag_mat_mul (#n: nat) (m1 m2: mat n)
  : Lemma (requires triangular_compat m1 m2 /\ unit_diag m1 /\ unit_diag m2)
          (ensures unit_diag (mat_mul m1 m2))
          [SMTPat (unit_diag (mat_mul m1 m2))] =
  match m1 with
  | MNil -> ()
  | MCons _ _ _ m1' -> let MCons _ _ _ m2' = m2 in unit_diag_mat_mul m1' m2'

let rec pos_diag_mat_mul (#n: nat) (m1 m2: mat n)
  : Lemma (requires triangular_compat m1 m2 /\ pos_diag m1 /\ pos_diag m2)
          (ensures pos_diag (mat_mul m1 m2))
          [SMTPat (pos_diag (mat_mul m1 m2))] =
  match m1 with
  | MNil -> ()
  | MCons _ _ _ m1' -> let MCons _ _ _ m2' = m2 in pos_diag_mat_mul m1' m2'

let rec nnz_diag_mat_mul (#n: nat) (m1 m2: mat n)
  : Lemma (requires triangular_compat m1 m2 /\ nnz_diag m1 /\ nnz_diag m2)
          (ensures nnz_diag (mat_mul m1 m2))
          [SMTPat (nnz_diag (mat_mul m1 m2))] =
  match m1 with
  | MNil -> ()
  | MCons _ _ _ m1' -> let MCons _ _ _ m2' = m2 in nnz_diag_mat_mul m1' m2'

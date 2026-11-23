module StructureTypes.Shape

open StructureTypes.Scalar
open StructureTypes.Vector
open StructureTypes.Matrix

let rec lower (#n: nat) (m: mat n) : prop =
  match m with
  | MNil -> True
  | MCons _ b _ m' -> is_zero_vec b /\ lower m'

let rec upper (#n: nat) (m: mat n) : prop =
  match m with
  | MNil -> True
  | MCons _ _ c m' -> is_zero_vec c /\ upper m'

let diagonal (#n: nat) (m: mat n) : prop = lower m /\ upper m

let rec unit_diag (#n: nat) (m: mat n) : prop =
  match m with
  | MNil -> True
  | MCons a _ _ m' -> is_one a /\ unit_diag m'

let rec pos_diag (#n: nat) (m: mat n) : prop =
  match m with
  | MNil -> True
  | MCons a _ _ m' -> is_pos a /\ pos_diag m'

let rec nnz_diag (#n: nat) (m: mat n) : prop =
  match m with
  | MNil -> True
  | MCons a _ _ m' -> is_nnz a /\ nnz_diag m'

let unit_lower (#n: nat) (m: mat n) : prop = lower m /\ unit_diag m

let symmetric (#n: nat) (m: mat n) : prop = m == transpose m

let triangular_compat (#n: nat) (m1 m2: mat n) : prop =
  (lower m1 /\ lower m2) \/ (upper m1 /\ upper m2)

let rec unit_diag_pos (#n: nat) (m: mat n)
  : Lemma (requires unit_diag m) (ensures pos_diag m) [SMTPat (pos_diag m)] =
  match m with
  | MNil -> ()
  | MCons _ _ _ m' -> unit_diag_pos m'

let rec pos_diag_nnz (#n: nat) (m: mat n)
  : Lemma (requires pos_diag m) (ensures nnz_diag m) [SMTPat (nnz_diag m)] =
  match m with
  | MNil -> ()
  | MCons _ _ _ m' -> pos_diag_nnz m'

let nnz_diag_top_left (#n: pos) (m: mat n)
  : Lemma (requires nnz_diag m) (ensures top_left_nnz m) [SMTPat (top_left_nnz m)] = ()

let rec id_mat_shape (#n: nat)
  : Lemma (lower (id_mat #n) /\ upper (id_mat #n) /\ unit_diag (id_mat #n))
          [SMTPatOr [[SMTPat (lower (id_mat #n))];
                     [SMTPat (upper (id_mat #n))];
                     [SMTPat (unit_diag (id_mat #n))]]] =
  if n = 0 then () else id_mat_shape #(n - 1)

let rec lower_mul (#n: nat) (m1 m2: mat n)
  : Lemma (requires lower m1 /\ lower m2) (ensures lower (mat_mul m1 m2))
          [SMTPat (lower (mat_mul m1 m2))] =
  match m1 with
  | MNil -> ()
  | MCons _ _ _ m1' -> let MCons _ _ _ m2' = m2 in lower_mul m1' m2'

let rec upper_mul (#n: nat) (m1 m2: mat n)
  : Lemma (requires upper m1 /\ upper m2) (ensures upper (mat_mul m1 m2))
          [SMTPat (upper (mat_mul m1 m2))] =
  match m1 with
  | MNil -> ()
  | MCons _ _ _ m1' -> let MCons _ _ _ m2' = m2 in upper_mul m1' m2'

let rec unit_diag_mul (#n: nat) (m1 m2: mat n)
  : Lemma (requires triangular_compat m1 m2 /\ unit_diag m1 /\ unit_diag m2)
          (ensures unit_diag (mat_mul m1 m2))
          [SMTPat (unit_diag (mat_mul m1 m2))] =
  match m1 with
  | MNil -> ()
  | MCons _ _ _ m1' -> let MCons _ _ _ m2' = m2 in unit_diag_mul m1' m2'

let rec pos_diag_mul (#n: nat) (m1 m2: mat n)
  : Lemma (requires triangular_compat m1 m2 /\ pos_diag m1 /\ pos_diag m2)
          (ensures pos_diag (mat_mul m1 m2))
          [SMTPat (pos_diag (mat_mul m1 m2))] =
  match m1 with
  | MNil -> ()
  | MCons _ _ _ m1' -> let MCons _ _ _ m2' = m2 in pos_diag_mul m1' m2'

let rec nnz_diag_mul (#n: nat) (m1 m2: mat n)
  : Lemma (requires triangular_compat m1 m2 /\ nnz_diag m1 /\ nnz_diag m2)
          (ensures nnz_diag (mat_mul m1 m2))
          [SMTPat (nnz_diag (mat_mul m1 m2))] =
  match m1 with
  | MNil -> ()
  | MCons _ _ _ m1' -> let MCons _ _ _ m2' = m2 in nnz_diag_mul m1' m2'

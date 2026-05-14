module MatrixType

open Scalar
open Vector

(* square matrices *)
noeq type mat : pos -> Type =
  | Mat1 : num -> mat 1
  | MatN : #n: pos -> mat n -> cvec n -> num -> rvec n -> mat (n + 1)

(* shapes *)
let rec lower (#n: pos) (m: mat n) : prop =
  match m with
  | Mat1 _ -> True
  | MatN m' _ _ row -> lower m' /\ is_zero_vec row

let rec upper (#n: pos) (m: mat n) : prop =
  match m with
  | Mat1 _ -> True
  | MatN m' col _ _ -> upper m' /\ is_zero_vec col

let diagonal (#n: pos) (m: mat n) : prop = lower m /\ upper m

(* what's on the diagonal *)
let rec unit_diag (#n: pos) (m: mat n) : prop =
  match m with
  | Mat1 a -> is_one a
  | MatN m' _ corner _ -> unit_diag m' /\ is_one corner

let rec nnz_diag (#n: pos) (m: mat n) : prop =
  match m with
  | Mat1 a -> is_nnz a
  | MatN m' _ corner _ -> nnz_diag m' /\ is_nnz corner

let rec pos_diag (#n: pos) (m: mat n) : prop =
  match m with
  | Mat1 a -> is_pos a
  | MatN m' _ corner _ -> pos_diag m' /\ is_pos corner

let rec pos_diag_nnz (#n: pos) (m: mat n)
    : Lemma (requires pos_diag m) (ensures nnz_diag m) [SMTPat (pos_diag m)] =
  match m with
  | Mat1 _ -> ()
  | MatN m' _ _ _ -> pos_diag_nnz m'

let rec unit_diag_pos (#n: pos) (m: mat n)
    : Lemma (requires unit_diag m) (ensures pos_diag m) [SMTPat (unit_diag m)] =
  match m with
  | Mat1 _ -> ()
  | MatN m' _ _ _ -> unit_diag_pos m'

(* properties *)
assume val rowsdd: #n: pos -> mat n -> prop
assume val spd: #n: pos -> mat n -> prop
assume val inv: #n: pos -> mat n -> prop

assume val spd_pos_diag (#n: pos) (m: mat n) : Lemma (requires spd m) (ensures pos_diag m) [SMTPat (spd m)]

assume val rowsdd_nnz_diag (#n: pos) (m: mat n)
    : Lemma (requires rowsdd m) (ensures nnz_diag m) [SMTPat (rowsdd m)]

assume val destruct_rowsdd (#n: pos{n >= 2}) (m: mat n)
    : Lemma (requires rowsdd m) (ensures (let MatN m' _ a _ = m in rowsdd m' /\ is_nnz a)) [SMTPat (rowsdd m)]

assume val destruct_spd (#n: pos{n >= 2}) (m: mat n)
    : Lemma (requires spd m) (ensures (let MatN m' _ a _ = m in spd m' /\ is_pos a)) [SMTPat (spd m)]

assume val inv_1x1_nnz_diag (m: mat 1)
    : Lemma (requires inv m) (ensures nnz_diag m) [SMTPat (inv (m <: mat 1))]

(* shorthands *)
let unit_lower (#n: pos) (m: mat n) : prop = lower m /\ unit_diag m

(* identity *)
let rec id_mat (#n: pos) : m:mat n{diagonal m /\ unit_diag m} =
  if n = 1 then Mat1 one else MatN (id_mat #(n - 1)) zero_cvec one zero_rvec

let is_id (#n: pos) (m: mat n) : prop = m == id_mat

(* zero matrix *)
let rec zero_mat (#n: pos) : mat n =
  if n = 1
  then Mat1 zero
  else MatN (zero_mat #(n - 1)) zero_cvec zero zero_rvec

let is_zero_mat (#n: pos) (m: mat n) : prop = m == zero_mat

(* permutation matrix *)
assume val perm: #n: pos -> mat n -> prop

assume val perm_is_inv (#n: pos) (m: mat n) : Lemma (requires perm m) (ensures inv m) [SMTPat (perm m)]

assume val id_mat_is_perm (#n: pos) : Lemma (perm (id_mat #n)) [SMTPat (id_mat #n)]

assume val augment_perm (#n: pos) (m: mat n) :
  Lemma (requires perm m) (ensures perm (MatN m zero_cvec one zero_rvec)) [SMTPat (perm m)]

(* top-left entry is nonzero *)
let top_left_nnz (#n: pos) (m: mat n) : prop =
  match m with
  | Mat1 a -> is_nnz a
  | MatN _ _ corner _ -> is_nnz corner

let nnz_diag_top_left (#n: pos) (m: mat n)
    : Lemma (requires nnz_diag m) (ensures top_left_nnz m) [SMTPat (nnz_diag m)] = ()
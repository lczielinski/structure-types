module MatrixType

open Scalar

(* square matrices *)
assume type mat : pos -> Type

(* shapes *)
assume val lower : #n:pos -> mat n -> prop
assume val upper : #n:pos -> mat n -> prop
let diagonal (#n:pos) (m:mat n) : prop = lower m /\ upper m

assume val one_by_one_lower : m:mat 1 -> Lemma (lower m) [SMTPat (lower m)]
assume val one_by_one_upper : m:mat 1 -> Lemma (upper m) [SMTPat (upper m)]

(* what's on the diagonal *)
assume val unit_diag : #n:pos -> mat n -> prop
assume val nnz_diag  : #n:pos -> mat n -> prop
assume val pos_diag  : #n:pos -> mat n -> prop

assume val pos_diag_nnz : #n:pos -> m:mat n ->
  Lemma (requires pos_diag m) (ensures nnz_diag m) [SMTPat (pos_diag m)]

assume val unit_diag_pos : #n:pos -> m:mat n ->
  Lemma (requires unit_diag m) (ensures pos_diag m) [SMTPat (unit_diag m)]

(* properties *)
assume val rowsdd : #n:pos -> mat n -> prop
assume val spd    : #n:pos -> mat n -> prop

assume val spd_pos_diag : #n:pos -> m:mat n ->
  Lemma (requires spd m) (ensures pos_diag m) [SMTPat (spd m)]

assume val rowsdd_nnz_diag : #n:pos -> m:mat n ->
  Lemma (requires rowsdd m) (ensures nnz_diag m) [SMTPat (rowsdd m)]

(* shorthands *)
let unit_lower (#n:pos) (m:mat n) : prop = lower m /\ unit_diag m

(* identity *)
assume val _id_mat : #n:pos -> m:mat n{diagonal m /\ unit_diag m}

let identity (#n:pos) (m:mat n) : prop = m == _id_mat

(* zero matrix *)
assume val _zero_mat : #n:pos -> mat n

let zero_mat (#n:pos) (m:mat n) : prop = m == _zero_mat
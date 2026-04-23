module MatrixType

open Scalar

(* square matrices *)
assume type mat : pos -> Type

(* shapes *)
assume val _lower : #n:pos -> mat(n) -> prop
assume val _upper : #n:pos -> mat(n) -> prop

(* diagonal *)
assume val _unit_diag : #n:pos -> mat(n) -> prop
assume val _nnz_diag : #n:pos -> mat(n) -> prop
assume val _pos_diag : #n:pos -> mat(n) -> prop

assume val pos_diag_nnz : #n:pos -> m:mat(n) ->
    Lemma (requires _pos_diag m) (ensures _nnz_diag m) [SMTPat (_pos_diag #n m)]

assume val unit_diag_pos : #n:pos -> m:mat(n) ->
    Lemma (requires _unit_diag m) (ensures _pos_diag m) [SMTPat (_unit_diag #n m)]

(* properties *)
assume val _rowsdd : #n:pos -> mat(n) -> prop
assume val _spd : #n:pos -> mat(n) -> prop

(* conversions *)
assume val spd_pos_diag : #n:pos -> m:mat(n) ->
    Lemma (requires _spd m) (ensures _pos_diag m)
    [SMTPat (_spd #n m)]

assume val rowsdd_nnz_diag : #n:pos -> m:mat(n) ->
    Lemma (requires _rowsdd m) (ensures _nnz_diag m)
    [SMTPat (_rowsdd #n m)]

let diag_pred (k:num_kind) : (#n:pos -> mat n -> prop) =
  match k with
  | Nnz -> _nnz_diag
  | Pos -> _pos_diag
  | One -> _unit_diag

let diag_of (k:num_kind) (n:pos) = m:mat(n){diag_pred k m}
let lower_of (k:num_kind) (n:pos) = m:mat n{_lower m /\ diag_pred k m}
let upper_of (k:num_kind) (n:pos) = m:mat n{_upper m /\ diag_pred k m}

let unit_lower = lower_of One
let pos_lower = lower_of Pos
let nnz_lower = lower_of Nnz
let diagonal (n:pos) = m:mat(n){_lower m /\ _upper m}
let spd (n:pos) = m:mat(n){_spd m}
let rowsdd (n:pos) = m:mat(n){_rowsdd m}
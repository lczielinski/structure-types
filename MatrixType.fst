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
    Lemma (requires _pos_diag m) (ensures _nnz_diag m)
    [SMTPat (_pos_diag m)]

assume val unit_diag_pos : #n:pos -> m:mat(n) ->
    Lemma (requires _unit_diag m) (ensures _pos_diag m)
    [SMTPat (_unit_diag m)]

(* properties *)
assume val _rowsdd : #n:pos -> mat(n) -> prop
assume val _spd : #n:pos -> mat(n) -> prop

(* conversions *)
assume val spd_pos_diag : #n:pos -> m:mat(n) ->
    Lemma (requires _spd m) (ensures _pos_diag m)
    [SMTPat (_spd m)]

assume val rowsdd_nnz_diag : #n:pos -> m:mat(n) ->
    Lemma (requires _rowsdd m) (ensures _nnz_diag m)
    [SMTPat (_rowsdd m)]

(* exposed types *)
let lower (n:pos) = m:mat(n){_lower m}
let upper (n:pos) = m:mat(n){_upper m}
let diag (n:pos) = m:mat(n){_lower m /\ _upper m}

let unit_diag (n:pos) = m:mat(n){_unit_diag m}
let pos_diag (n:pos) = m:mat(n){_pos_diag m}
let nnz_diag (n:pos) = m:mat(n){_nnz_diag m}

let spd (n:pos) = m:mat(n){_spd m}
let rowsdd (n:pos) = m:mat(n){_rowsdd m}

let unit_lower (n:pos) = m:mat(n){_lower m /\ _unit_diag m}
let pos_lower (n:pos) = m:mat(n){_lower m /\ _pos_diag m}
let nnz_lower (n:pos) = m:mat(n){_lower m /\ _nnz_diag m}

(* kinds *)
noeq type diag_kind = { pred : #n:pos -> mat n -> prop; num_kind : num_kind }

let unit_kind : diag_kind = { pred = (fun #n m -> _unit_diag m); num_kind = one_kind }
let pos_kind : diag_kind = { pred = (fun #n m -> _pos_diag m); num_kind = pos_kind }
let nnz_kind : diag_kind = { pred = (fun #n m -> _nnz_diag m); num_kind = nnz_kind }

let witness (k:diag_kind) = num_of k.num_kind
let lower_of (k:diag_kind) (n:pos) = m:mat(n){ _lower m /\ k.pred m }


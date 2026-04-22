module MatrixType

(* square matrices *)
assume type mat : pos -> Type

(* shapes *)
assume val lower : #n:pos -> mat n -> prop
assume val upper : #n:pos -> mat n -> prop
let diag (#n:pos) (m:mat n) : prop = lower m /\ upper m

(* diagonal *)
assume val unit_diag : #n:pos -> mat n -> prop
assume val nnz_diag : #n:pos -> mat n -> prop
assume val pos_diag : #n:pos -> mat n -> prop

assume val pos_diag_nnz : #n:pos -> m:mat n ->
    Lemma (requires pos_diag m) (ensures nnz_diag m)
    [SMTPat (pos_diag m)]

assume val unit_diag_pos : #n:pos -> m:mat n ->
    Lemma (requires unit_diag m) (ensures pos_diag m)
    [SMTPat (unit_diag m)]

(* properties *)
assume val rowsdd : #n:pos -> mat n -> prop
assume val spd : #n:pos -> mat n -> prop

(* conversions *)
assume val spd_pos_diag : #n:pos -> m:mat n ->
    Lemma (requires spd m) (ensures pos_diag m)
    [SMTPat (spd m)]

assume val rowsdd_nnz_diag : #n:pos -> m:mat n ->
    Lemma (requires rowsdd m) (ensures nnz_diag m)
    [SMTPat (rowsdd m)]

let unit_lower (n:pos) = m:mat n {lower m /\ unit_diag m}
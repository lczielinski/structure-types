module Structure

(* scalars *)
type num = | R | NNZ | Pos
assume type scalar : num -> Type

let num_compat (specific general : num) : bool =
    general = R || specific = general ||
    (specific = Pos && general = NNZ)

assume val coerce_scalar : #n1:num -> #n2:num{num_compat n1 n2} ->
    scalar n1 -> scalar n2

// could do refinement type: 

(* vectors *)    
assume type cvec : pos -> Type
assume type rvec : pos -> Type

(* matrices *)
type shape = | AnyShape | Upper | Lower | Diagonal
type diagonal = | AnyDiag | UnitDiag | NNZDiag | PosDiag
type property = | AnyProp | RowSDD | SPD
    
let shape_compat (specific general : shape) (n : pos) : bool =
    general = AnyShape || specific = general || n = 1 ||
    (specific = Diagonal && (general = Upper || general = Lower))
    
let diag_compat (specific general : diagonal) (p : property) : bool =
    general = AnyDiag || specific = general ||
    (specific = UnitDiag && (general = NNZDiag || general = PosDiag)) ||
    (specific = PosDiag && general = NNZDiag) ||
    ((p = RowSDD || p = SPD) && general = NNZDiag) ||
    (p = SPD && general = PosDiag)
    
let prop_compat (specific general : property) (n : pos) : bool =
    general = AnyProp || specific = general || n = 1
    
assume type sq_mat : pos -> shape -> diagonal -> property -> Type
    
(* matrix subtyping *)
assume val coerce : #n:pos ->
    #s1:shape -> #s2:shape{shape_compat s1 s2 n} ->
    #p1:property -> #p2:property{prop_compat p1 p2 n} ->
    #d1:diagonal -> #d2:diagonal{diag_compat d1 d2 p1} ->
    sq_mat n s1 d1 p1 -> sq_mat n s2 d2 p2
    
(* destructors *)
assume val destruct_nnzdiag : #n:pos -> #s:shape -> #p:property ->
    sq_mat (n + 1) s NNZDiag p ->
    cvec n * scalar NNZ * rvec n * sq_mat n s NNZDiag p

assume val destruct_posdiag : #n:pos -> #s:shape -> #p:property ->
    sq_mat (n + 1) s PosDiag p ->
    cvec n * scalar Pos * rvec n * sq_mat n s PosDiag p
  
(* preserves SDD and SPD *)
assume val schur1 : #n:pos -> #s:shape -> #d:diagonal -> #p:property ->
    sq_mat (n + 1) s d p -> sq_mat n s AnyDiag p
// would need to know a fact about it

(* augment *)
assume val augment_lower_unitdiag : #n:pos -> #p:property ->
    sq_mat n Lower UnitDiag p -> cvec n ->
    sq_mat (n + 1) Lower UnitDiag AnyProp

assume val augment_lower_posdiag : #n:pos -> #p:property ->
    sq_mat n Lower PosDiag p -> cvec n -> scalar Pos -> 
    sq_mat (n + 1) Lower PosDiag AnyProp

assume val augment_upper_nnzdiag : #n:pos -> #p:property ->
    sq_mat n Upper NNZDiag p -> scalar NNZ -> rvec n ->
    sq_mat (n + 1) Upper NNZDiag AnyProp

(* scalars *)
assume val extract_scalar : #s:shape -> #p:property ->
    sq_mat 1 s NNZDiag p -> scalar NNZ
    
assume val singleton_unit : sq_mat 1 AnyShape UnitDiag AnyProp
assume val singleton : scalar NNZ -> sq_mat 1 AnyShape NNZDiag AnyProp

assume val col_div : #n:pos -> cvec n -> scalar NNZ -> cvec n
assume val sqrt : scalar Pos -> scalar Pos

(* LU function *)
val lu : #n:pos -> sq_mat n AnyShape NNZDiag RowSDD ->
    sq_mat n Lower UnitDiag AnyProp * sq_mat n Upper NNZDiag AnyProp

let rec lu #n m =
    if n = 1 then
        (coerce singleton_unit, coerce m)
    else
        let (c, a, b, _) = destruct_nnzdiag #(n - 1) m in
        let s  = schur1 m in
        let (l, u) = lu (coerce s) in
        let d  = col_div c a in
        let l' = augment_lower_unitdiag l d in
        let u' = augment_upper_nnzdiag u a b in
        (l', u')

(* Cholesky *)
val cholesky : #n:pos -> sq_mat n AnyShape PosDiag SPD ->
    sq_mat n Lower PosDiag AnyProp

let rec cholesky #n m =
    if n = 1 then
        (coerce m)
    else
        let (c, a, b, _) = destruct_posdiag #(n - 1) m in
        let s = schur1 m in
        let l11 = sqrt a in
        let l21 = col_div c (coerce_scalar l11) in
        let l = cholesky (coerce s) in
        augment_lower_posdiag l l21 l11


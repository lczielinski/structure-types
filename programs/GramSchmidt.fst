module GramSchmidt

open All

noeq type rect : pos -> pos -> Type = 
  | Rect1 : #n:pos -> cvec n -> rect n 1
  | RectK : #n:pos -> #k:pos -> rect n k -> cvec n -> rect n (k + 1)

assume val nnz_vec  (#n:pos) (#o:orient) (v:vec o n) : prop
assume val unit_vec (#n:pos) (#o:orient) (v:vec o n) : prop

assume val unit_vec_nnz (#n:pos) (#o:orient) (v:vec o n) :
    Lemma (requires unit_vec v) (ensures nnz_vec v) [SMTPat (nnz_vec v)]

(* v is linearly independent of the columns of m *)
assume val mat_vec_ind (#n:pos) (#k:pos) (m:rect n k) (v:cvec n) : prop
(* v is orthogonal to every column of m *)
assume val mat_vec_ortho (#n:pos) (#k:pos) (m:rect n k) (v:cvec n) : prop

assume val ortho_nnz (#n:pos) (#k:pos) (m:rect n k) (v:cvec n) :
    Lemma (requires mat_vec_ortho m v) (ensures nnz_vec v) [SMTPat (mat_vec_ortho m v)]
assume val ortho_is_ind (#n:pos) (#k:pos) (m:rect n k) (v:cvec n) :
    Lemma (requires mat_vec_ortho m v) (ensures mat_vec_ind m v) [SMTPat (mat_vec_ortho m v)]

(* entire matrix has lin ind/ortho cols *)
let rec linind (#n:pos) (#k:pos) (m:rect n k) : prop = 
  match m with 
  | Rect1 v -> nnz_vec v 
  | RectK m' v -> linind m' /\ mat_vec_ind m' v /\ nnz_vec v

let rec ortho (#n:pos) (#k:pos) (m:rect n k) : prop = 
  match m with 
  | Rect1 v -> unit_vec v
  | RectK m' v -> ortho m' /\ mat_vec_ortho m' v /\ unit_vec v

let same_col_span (#n:pos) (#k:pos) (m1 m2:rect n k) : prop =
  forall (v:cvec n). mat_vec_ind m1 v <==> mat_vec_ind m2 v

assume val span_pres_ortho (#n:pos) (#k:pos) (m1 m2:rect n k) :
    Lemma (requires same_col_span m1 m2)
          (ensures forall (v:cvec n). mat_vec_ortho m1 v <==> mat_vec_ortho m2 v)
          [SMTPat (same_col_span m1 m2)]

(* can append a column *)
assume val vec_span_cong (#n:pos) (v1 v2:cvec n) :
    Lemma (requires same_col_span (Rect1 v1) (Rect1 v2))
          (ensures forall (#k:pos) (m:rect n k).
                     same_col_span (RectK m v1) (RectK m v2) /\
                     (mat_vec_ortho m v1 <==> mat_vec_ortho m v2) /\
                     (mat_vec_ind m v1 <==> mat_vec_ind m v2))
          [SMTPat (same_col_span (Rect1 v1) (Rect1 v2))]

assume val mat_span_cong (#n:pos) (#k:pos) (m1 m2:rect n k) :
    Lemma (requires same_col_span m1 m2)
          (ensures forall (v:cvec n).
                     same_col_span (RectK m1 v) (RectK m2 v))
          [SMTPat (same_col_span m1 m2)]

(* operations *)
assume val normalize (#n:pos) (v1:cvec n{nnz_vec v1}) : (v2:cvec n{unit_vec v2})

assume val normalize_pres_span (#n:pos) (v:cvec n{nnz_vec v}) :
    Lemma (same_col_span (Rect1 v) (Rect1 (normalize v)))
          [SMTPat (normalize v)]

assume val residual (#n:pos) (#k:pos) (m:rect n k)
    (v1:cvec n{mat_vec_ind m v1}) : v2:cvec n{mat_vec_ortho m v2 /\ same_col_span (RectK m v1) (RectK m v2)}

assume val residual_mat (#n:pos) (#k:pos) (v:cvec n{unit_vec v}) (m1:rect n k) : 
  m2:rect n k{mat_vec_ortho m2 v /\ linind m2 /\ same_col_span (RectK m1 v) (RectK m2 v)}

(* regular gram schmidt *)
let rec gramschmidt (#n:pos) (#k:pos) (m:rect n k{linind m}) : 
  (q:rect n k{ortho q /\ same_col_span m q}) = 
  match m with 
  | Rect1 v -> Rect1 (normalize v)
  | RectK m' v -> 
    // assert mat_vec_ind m' v;
    let q' = gramschmidt m' in
    // assert mat_vec_ind q' v;
    // assert same_col_span (RectK m' v) (RectK q' v);
    let res = residual q' v in
    // assert same_col_span (RectK q' v) (RectK q' res);
    let q = normalize res in
    // assert same_col_span (RectK q' res) (RectK q' q);
    // assert same_col_span (RectK m' v) (RectK q' q);
    let r = RectK q' q in
    // assert same_col_span m r;
    // assert mat_vec_ortho q' res;
    // assert mat_vec_ortho q' q;
    r

(* modified gram schmidt *)
let rec mgs (#n:pos) (#k:pos) (m:rect n k{linind m}) : 
  (q:rect n k{ortho q /\ same_col_span m q}) = 
  match m with 
  | Rect1 v -> Rect1 (normalize v)
  | RectK m' v -> 
    let q1 = normalize v in
    let m'' = residual_mat q1 m' in 
    let q = mgs m'' in 
    RectK q q1
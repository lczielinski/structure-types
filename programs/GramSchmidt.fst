module GramSchmidt

open StructureTypes.All

noeq type rect : pos -> pos -> Type = 
  | Rect1 : #n:pos -> cvec n -> rect n 1
  | RectK : #n:pos -> #k:pos -> rect n k -> cvec n -> rect n (k + 1)

assume val vec_is_nnz  (#n:pos) (v:vec n) : prop
assume val vec_is_unit (#n:pos) (v:vec n) : prop

assume val vec_unit_nnz (#n:pos) (v:vec n) :
    Lemma (requires vec_is_unit v) (ensures vec_is_nnz v) [SMTPat (vec_is_nnz v)]

(* v is linearly independent of the columns of m *)
assume val rect_vec_ind (#n:pos) (#k:pos) (m:rect n k) (v:cvec n) : prop
(* v is orthogonal to every column of m *)
assume val rect_vec_ortho (#n:pos) (#k:pos) (m:rect n k) (v:cvec n) : prop

// check
assume val rect_vec_ortho_nnz (#n:pos) (#k:pos) (m:rect n k) (v:cvec n) :
    Lemma (requires rect_vec_ortho m v) (ensures vec_is_nnz v) [SMTPat (rect_vec_ortho m v)]
assume val rect_vec_ortho_ind (#n:pos) (#k:pos) (m:rect n k) (v:cvec n) :
    Lemma (requires rect_vec_ortho m v) (ensures rect_vec_ind m v) [SMTPat (rect_vec_ortho m v)]

(* entire matrix has lin ind/orthonormal cols *)
let rec lin_indep (#n:pos) (#k:pos) (m:rect n k) : prop = 
  match m with 
  | Rect1 v -> vec_is_nnz v 
  | RectK m' v -> lin_indep m' /\ rect_vec_ind m' v /\ vec_is_nnz v

let rec orthonormal (#n:pos) (#k:pos) (m:rect n k) : prop = 
  match m with 
  | Rect1 v -> vec_is_unit v
  | RectK m' v -> orthonormal m' /\ rect_vec_ortho m' v /\ vec_is_unit v

let same_col_span (#n:pos) (#k:pos) (m1 m2:rect n k) : prop =
  forall (v:cvec n). rect_vec_ind m1 v <==> rect_vec_ind m2 v

assume val same_col_span_ortho (#n:pos) (#k:pos) (m1 m2:rect n k) :
    Lemma (requires same_col_span m1 m2)
          (ensures forall (v:cvec n). rect_vec_ortho m1 v <==> rect_vec_ortho m2 v)
          [SMTPat (same_col_span m1 m2)]

(* can append a column *)
assume val same_col_span_cong_vec (#n:pos) (v1 v2:cvec n) :
    Lemma (requires same_col_span (Rect1 v1) (Rect1 v2))
          (ensures forall (#k:pos) (m:rect n k).
                     same_col_span (RectK m v1) (RectK m v2) /\
                     (rect_vec_ortho m v1 <==> rect_vec_ortho m v2) /\
                     (rect_vec_ind m v1 <==> rect_vec_ind m v2))
          [SMTPat (same_col_span (Rect1 v1) (Rect1 v2))]

assume val same_col_span_cong_rect (#n:pos) (#k:pos) (m1 m2:rect n k) :
    Lemma (requires same_col_span m1 m2)
          (ensures forall (v:cvec n).
                     same_col_span (RectK m1 v) (RectK m2 v))
          [SMTPat (same_col_span m1 m2)]

(* operations *)
assume val vec_normalize (#n:pos) (v1:cvec n{vec_is_nnz v1}) : (v2:cvec n{vec_is_unit v2})

assume val vec_normalize_span (#n:pos) (v:cvec n{vec_is_nnz v}) :
    Lemma (same_col_span (Rect1 v) (Rect1 (vec_normalize v)))
          [SMTPat (vec_normalize v)]

assume val vec_norm (#n:pos) (v:cvec n) : num

assume val rect_vec_residual (#n:pos) (#k:pos) (m:rect n k)
    (v1:cvec n{rect_vec_ind m v1}) : v2:cvec n{rect_vec_ortho m v2 /\ same_col_span (RectK m v1) (RectK m v2)}

assume val vec_rect_residual (#n:pos) (#k:pos) (v:cvec n{vec_is_unit v}) (m1:rect n k{lin_indep m1 /\ rect_vec_ind m1 v}) : 
  m2:rect n k{rect_vec_ortho m2 v /\ lin_indep m2 /\ same_col_span (RectK m1 v) (RectK m2 v)}
// why is m2 still lin_indep

(* regular gram schmidt *)
let rec gram_schmidt (#n:pos) (#k:pos) (m:rect n k{lin_indep m}) : 
  (q:rect n k{orthonormal q /\ same_col_span m q}) = 
  match m with 
  | Rect1 v -> Rect1 (vec_normalize v)
  | RectK m' v -> 
    // assert rect_vec_ind m' v;
    let q' = gram_schmidt m' in
    // assert rect_vec_ind q' v;
    // assert same_col_span (RectK m' v) (RectK q' v);
    let res = rect_vec_residual q' v in
    // assert same_col_span (RectK q' v) (RectK q' res);
    let q = vec_normalize res in
    // assert same_col_span (RectK q' res) (RectK q' q);
    // assert same_col_span (RectK m' v) (RectK q' q);
    let q'' = RectK q' q in
    // assert same_col_span m r;
    // assert rect_vec_ortho q' res;
    // assert rect_vec_ortho q' q;
    q''

let rec gram_schmidt_qr (#n:pos) (#k:pos) (m:rect n k{lin_indep m}) : 
  (q:rect n k{orthonormal q /\ same_col_span m q}) & (r:mat k{upper r}) = 
  match m with 
  | Rect1 v -> 
    let q = Rect1 (vec_normalize v) in 
    let r = MCons (vec_norm v) VNil VNil MNil in 
    (q, r)
  | RectK m' v -> 
    // assert rect_vec_ind m' v;
    let q' = gram_schmidt m' in
    // assert rect_vec_ind q' v;
    // assert same_col_span (RectK m' v) (RectK q' v);
    let res = rect_vec_residual q' v in
    // assert same_col_span (RectK q' v) (RectK q' res);
    let q = vec_normalize res in
    // assert same_col_span (RectK q' res) (RectK q' q);
    // assert same_col_span (RectK m' v) (RectK q' q);
    let r = RectK q' q in
    // assert same_col_span m r;
    // assert rect_vec_ortho q' res;
    // assert rect_vec_ortho q' q;
    magic()

(* modified gram schmidt *)
let rec modified_gram_schmidt (#n:pos) (#k:pos) (m:rect n k{lin_indep m}) : 
  (q:rect n k{orthonormal q /\ same_col_span m q}) = 
  match m with 
  | Rect1 v -> Rect1 (vec_normalize v)
  | RectK m' v -> 
    let q1 = vec_normalize v in
    let m'' = vec_rect_residual q1 m' in 
    let q = modified_gram_schmidt m'' in 
    RectK q q1
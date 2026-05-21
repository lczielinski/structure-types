module GramSchmidt

open All

noeq type rect : pos -> pos -> Type = 
  | Rect1 : #n:pos -> cvec n -> rect n 1
  | RectK : #n:pos -> #k:pos -> rect n k -> cvec n -> rect n (k + 1)

assume val nnz_vec (#n:pos) (#o:orient) (v:vec o n) : prop
assume val unit_vec (#n:pos) (#o:orient) (v:vec o n) : prop
assume val unit_vec_nnz (#n:pos) (#o:orient) (v:vec o n) : 
    Lemma (requires unit_vec v) (ensures nnz_vec v) [SMTPat (nnz_vec v)]

assume val linind (#n:pos) (#k:pos) (m:rect n k) : prop
assume val one_linind (#n:pos) (m:rect n 1) : 
  Lemma (requires linind m) (ensures (let Rect1 v = m in nnz_vec v))
  [SMTPat (linind m)]
assume val linind_one (#n:pos) (v:cvec n) :
  Lemma (requires nnz_vec v) (ensures linind (Rect1 v)) [SMTPat (Rect1 v)]
assume val destruct_linind (#n:pos) (#k:pos{k>=2}) (m:rect n k) : 
  Lemma (requires linind m) (ensures (let RectK m' v = m in linind m' /\ nnz_vec v))
  [SMTPat (linind m)]

assume val ortho (#n:pos) (#k:pos) (m:rect n k) : prop
assume val one_ortho (#n:pos) (m:rect n 1) : 
  Lemma (requires ortho m) (ensures (let Rect1 v = m in nnz_vec v))
  [SMTPat (ortho m)]
assume val ortho_one (#n:pos) (v:cvec n) : 
  Lemma (requires unit_vec v) (ensures ortho (Rect1 v)) [SMTPat (Rect1 v)]
assume val destruct_ortho (#n:pos) (#k:pos{k>=2}) (m:rect n k) : 
  Lemma (requires ortho m) (ensures (let RectK m' v = m in ortho m' /\ unit_vec v))
  [SMTPat (ortho m)]

assume val ortho_span (#n:pos) (#k:pos) (m:rect n k) (v:cvec n) : prop

assume val normalize (#n:pos) (#o:orient) (v1:vec o n{nnz_vec v1}) : 
  (v2:vec o n{unit_vec v2})

assume val residual (#n:pos) (#k:pos) (m:rect n k) 
  (v1:cvec n{ortho_span m v1}) : v2:cvec n{nnz_vec v2}

// let rec gramschmidt (#n:pos) (#k:pos) (m:rect n k{linind m}) : 
//   (q:rect n k{ortho q}) = 
//   match m with 
//   | Rect1 v -> Rect1 (normalize v)
//   | RectK m' v -> 
//     let q' = gramschmidt m' in
//     let res = residual q' v in
//     let q = normalize res in
//     RectK q' q

module Scalar

assume type num : Type

assume val _nnz : num -> prop
assume val _pos : num -> prop
assume val _one : num -> prop

assume val pos_is_nnz : r:num ->
    Lemma (requires _pos r) (ensures _nnz r) [SMTPat (_pos r)]

assume val one_is_pos : r:num ->
    Lemma (requires _one r) (ensures _pos r) [SMTPat (_one r)]

type num_kind = | Nnz | Pos | One

let pred_of (k:num_kind) : num -> prop =
  match k with
  | Nnz -> _nnz
  | Pos -> _pos
  | One -> _one

let num_of (k:num_kind) = r:num{pred_of k r}

let nnz = num_of Nnz
let posr = num_of Pos
let one = num_of One

assume val one_const : one

assume val scalar_mul : #k:num_kind -> num_of k -> num_of k -> num_of k

assume val scalar_mul_one_r : #k:num_kind -> r:num_of k -> o:one ->
    Lemma (ensures scalar_mul r o == r)
    [SMTPat (scalar_mul r o)]

assume val scalar_mul_one_l : #k:num_kind -> r:num_of k -> o:one ->
    Lemma (ensures scalar_mul #k o r == r)
    [SMTPat (scalar_mul #k o r)]

assume val one_unique : o1:one -> o2:one->
    Lemma (ensures o1 == o2)
    [SMTPat o1; SMTPat o2]

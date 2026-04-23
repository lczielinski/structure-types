module Scalar

assume type num : Type

assume val _nnz : num -> prop
assume val _pos : num -> prop
assume val _one : num -> prop

assume val pos_is_nnz : r:num ->
    Lemma (requires _pos r) (ensures _nnz r)
    [SMTPat (_pos r)]

assume val one_is_pos : r:num ->
    Lemma (requires _one r) (ensures _pos r)
    [SMTPat (_one r)]

noeq type num_kind = { pred : num -> prop }

let pos_kind : num_kind = { pred = _pos }
let nnz_kind : num_kind = { pred = _nnz }
let one_kind : num_kind = { pred = _one }

let num_of (k:num_kind) = r:num{k.pred r}

assume val scalar_mul : #k:num_kind -> num_of k -> num_of k -> num_of k

(* exposed types *)
let nnz = r:num{_nnz r}
let posr = r:num{_pos r}
let one = r:num{_one r}

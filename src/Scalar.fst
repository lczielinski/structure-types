module Scalar

assume type num : Type

assume val _one  : num
assume val _zero : num

assume val posr : num -> prop

let one  (a:num) : prop = a == _one
let zero (a:num) : prop = a == _zero
let nnz  (a:num) : prop = ~(zero a)

assume val one_is_pos : a:num ->
  Lemma (requires one a) (ensures posr a) [SMTPat (one a)]

assume val pos_is_nnz : a:num ->
  Lemma (requires posr a) (ensures nnz a) [SMTPat (posr a)]

assume val scalar_mul : a1:num -> a2:num -> a3:num{
  (one a1 ==> a3 == a2) /\
  (one a2 ==> a3 == a1) /\
  (posr a1 /\ posr a2 ==> posr a3) /\
  (nnz  a1 /\ nnz  a2 ==> nnz  a3) /\
  (zero a1 \/ zero a2 ==> zero a3)
}

assume val scalar_add : a1:num -> a2:num -> a3:num{
  (zero a1 ==> a2 == a3) /\
  (zero a2 ==> a1 == a3) /\
  (posr a1 /\ posr a2 ==> posr a3)
}

assume val sqrt : a1:num{posr a1} -> a2:num{
  posr a2 /\ scalar_mul a2 a2 == a1
}

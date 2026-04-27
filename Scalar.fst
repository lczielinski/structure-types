module Scalar

assume type num : Type

assume val nnz : num -> prop
assume val posr : num -> prop
assume val one : num -> prop

assume val pos_is_nnz : a:num ->
    Lemma (requires posr a) (ensures nnz a) [SMTPat (posr a)]

assume val one_is_pos : a:num ->
    Lemma (requires one a) (ensures posr a) [SMTPat (one a)]

assume val scalar_mul : a1:num -> a2:num -> a3:num {
    (one a1 ==> a3 == a2) /\ (one a2 ==> a3 == a1) /\
    (posr a1 /\ posr a2 ==> posr a3) /\
    (nnz a1 /\ nnz a2 ==> nnz a3)
}

assume val _one : a:num{one a}

assume val one_unique : a:num ->
  Lemma (requires one a) (ensures a == _one)
  [SMTPat (one a)]

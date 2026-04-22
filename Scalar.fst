module Scalar

assume type num : Type

assume val nnz : num -> prop
assume val positive : num -> prop

assume val positive_is_nnz : r:num->
    Lemma (requires positive r) (ensures nnz r)
    [SMTPat (positive r)]

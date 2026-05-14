module Scalar

assume type num : Type

assume val one : num
assume val zero : num

assume val is_pos : num -> prop
let is_one (a: num) : prop = a == one
let is_zero (a: num) : prop = a == zero
let is_nnz (a: num) : prop = ~(is_zero a)
let is_nneg (a: num) : prop = is_pos a \/ is_zero a

assume val one_is_pos (a: num) : Lemma (requires is_one a) (ensures is_pos a) [SMTPat (is_one a)]

assume val pos_is_nnz (a: num) : Lemma (requires is_pos a) (ensures is_nnz a) [SMTPat (is_pos a)]

(* multiplication *)
assume val scalar_mul (a1 a2: num) : a3: num
      { (is_one a1 ==> a3 == a2) /\ (is_one a2 ==> a3 == a1) /\
        (is_pos a1 /\ is_pos a2 ==> is_pos a3) /\ (is_nnz a1 /\ is_nnz a2 ==> is_nnz a3) /\
        (is_zero a1 \/ is_zero a2 ==> is_zero a3) }

assume val scalar_add (a1 a2: num) : a3: num
      { (is_zero a1 ==> a2 == a3) /\ (is_zero a2 ==> a1 == a3) /\
        (is_pos a1 /\ is_pos a2 ==> is_pos a3) }

assume val sqrt (a1: num{is_nneg a1})
    : a2:num{(is_pos a1 ==> is_pos a2) /\ (is_zero a1 ==> is_zero a2) /\ scalar_mul a2 a2 == a1}

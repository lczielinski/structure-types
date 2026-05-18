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

assume val scalar_mul_assoc (a b c: num)
    : Lemma (scalar_mul (scalar_mul a b) c == scalar_mul a (scalar_mul b c))

(* division *)
assume val scalar_div (a1: num) (a2: num{is_nnz a2}) : a3: num{scalar_mul a3 a2 == a1}

assume val scalar_mul_div_comm (a b: num) (l: num{is_nnz l})
    : Lemma (scalar_mul a (scalar_div b l) == scalar_mul (scalar_div a l) b)

assume val scalar_div_assoc (a1: num) (a2: num{is_nnz a2}) (a3: num{is_nnz a3})
    : Lemma (scalar_div (scalar_div a1 a2) a3 == scalar_div a1 (scalar_mul a2 a3))
      [SMTPat (scalar_div (scalar_div a1 a2) a3)]

(* addition *)
assume val scalar_add (a1 a2: num) : a3: num
      { (is_zero a1 ==> a2 == a3) /\ (is_zero a2 ==> a1 == a3) /\
        (is_pos a1 /\ is_pos a2 ==> is_pos a3) }

assume val scalar_add_comm (a b: num)
    : Lemma (scalar_add a b == scalar_add b a)

assume val scalar_add_assoc (a b c: num)
    : Lemma (scalar_add (scalar_add a b) c == scalar_add a (scalar_add b c))

assume val scalar_mul_add_dist_r (a1 a2 a3: num)
    : Lemma (scalar_mul (scalar_add a1 a2) a3 == scalar_add (scalar_mul a1 a3) (scalar_mul a2 a3))
      [SMTPat (scalar_mul (scalar_add a1 a2) a3)]

(* square root *)
assume val sqrt (a1: num{is_nneg a1})
    : a2:num{(is_pos a1 ==> is_pos a2) /\ (is_zero a1 ==> is_zero a2) /\ scalar_mul a2 a2 == a1}

(* negate *)
assume val scalar_neg (a1: num) : a2: num
      { scalar_add a1 a2 == zero /\ scalar_add a2 a1 == zero /\ (is_zero a1 <==> is_zero a2) }

assume val scalar_neg_involutive (a: num)
    : Lemma (scalar_neg (scalar_neg a) == a) [SMTPat (scalar_neg (scalar_neg a))]

assume val scalar_neg_add_dist (a1 a2: num)
    : Lemma (scalar_neg (scalar_add a1 a2) == scalar_add (scalar_neg a1) (scalar_neg a2))
      [SMTPat (scalar_neg (scalar_add a1 a2))]

assume val scalar_mul_neg (a1 a2: num)
    : Lemma (scalar_mul a1 (scalar_neg a2) == scalar_neg (scalar_mul a1 a2))
      [SMTPat (scalar_mul a1 (scalar_neg a2))]

(* subtraction *)
let scalar_sub (a1 a2: num) : num = scalar_add a1 (scalar_neg a2)
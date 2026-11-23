module StructureTypes.Scalar

assume type num : Type0

assume val scalar_one : num
assume val scalar_zero : num

assume val scalar_is_pos : num -> prop
let scalar_is_one (a: num) : prop = a == scalar_one
let scalar_is_zero (a: num) : prop = a == scalar_zero
let scalar_is_nnz (a: num) : prop = ~(scalar_is_zero a)
let scalar_is_nneg (a: num) : prop = scalar_is_pos a \/ scalar_is_zero a

assume val scalar_one_pos (a: num) : Lemma (requires scalar_is_one a) (ensures scalar_is_pos a) [SMTPat (scalar_is_one a)]

assume val scalar_pos_nnz (a: num) : Lemma (requires scalar_is_pos a) (ensures scalar_is_nnz a) [SMTPat (scalar_is_pos a)]

(* multiplication *)
assume val scalar_mul (a1 a2: num) : a3: num
      { (scalar_is_one a1 ==> a3 == a2) /\ (scalar_is_one a2 ==> a3 == a1) /\
        (scalar_is_pos a1 /\ scalar_is_pos a2 ==> scalar_is_pos a3) /\ (scalar_is_nnz a1 /\ scalar_is_nnz a2 ==> scalar_is_nnz a3) /\
        (scalar_is_zero a1 \/ scalar_is_zero a2 ==> scalar_is_zero a3) }

assume val scalar_mul_assoc (a b c: num)
    : Lemma (scalar_mul (scalar_mul a b) c == scalar_mul a (scalar_mul b c))

assume val scalar_mul_comm (a b: num)
    : Lemma (scalar_mul a b == scalar_mul b a)

(* division *)
assume val scalar_div (a1: num) (a2: num{scalar_is_nnz a2}) : a3: num{scalar_mul a3 a2 == a1}

(* addition *)
assume val scalar_add (a1 a2: num) : a3: num
      { (scalar_is_zero a1 ==> a2 == a3) /\ (scalar_is_zero a2 ==> a1 == a3) /\
        (scalar_is_pos a1 /\ scalar_is_pos a2 ==> scalar_is_pos a3) }

assume val scalar_add_comm (a b: num)
    : Lemma (scalar_add a b == scalar_add b a)

assume val scalar_add_assoc (a b c: num)
    : Lemma (scalar_add (scalar_add a b) c == scalar_add a (scalar_add b c))

assume val scalar_mul_add_l (a1 a2 a3: num)
    : Lemma (scalar_mul (scalar_add a1 a2) a3 == scalar_add (scalar_mul a1 a3) (scalar_mul a2 a3))
      [SMTPat (scalar_mul (scalar_add a1 a2) a3)]

(* square root *)
assume val scalar_sqrt (a1: num{scalar_is_nneg a1})
    : a2:num{(scalar_is_pos a1 ==> scalar_is_pos a2) /\ (scalar_is_zero a1 ==> scalar_is_zero a2) /\ scalar_mul a2 a2 == a1}

(* negate *)
assume val scalar_neg (a1: num) : a2: num
      { scalar_add a1 a2 == scalar_zero /\ scalar_add a2 a1 == scalar_zero /\ (scalar_is_zero a1 <==> scalar_is_zero a2) }

(* subtraction *)
let scalar_sub (a1 a2: num) : num = scalar_add a1 (scalar_neg a2)

module StructureTypes.Scalar

assume type num : Type0

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

assume val scalar_mul_comm (a b: num)
    : Lemma (scalar_mul a b == scalar_mul b a)

(* division *)
assume val scalar_div (a1: num) (a2: num{is_nnz a2}) : a3: num{scalar_mul a3 a2 == a1}

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

(* derived facts *)
let scalar_mul_add_dist_l (a b c: num)
    : Lemma (scalar_mul a (scalar_add b c) == scalar_add (scalar_mul a b) (scalar_mul a c)) =
  scalar_mul_comm a (scalar_add b c);
  scalar_mul_comm b a;
  scalar_mul_comm c a

(* additive inverses are unique *)
let scalar_neg_unique (a b: num)
    : Lemma (requires scalar_add a b == zero) (ensures b == scalar_neg a) =
  calc (==) {
    (b <: num);
    == { }
    scalar_add zero b;
    == { }
    scalar_add (scalar_add (scalar_neg a) a) b;
    == { scalar_add_assoc (scalar_neg a) a b }
    scalar_add (scalar_neg a) (scalar_add a b);
    == { }
    scalar_neg a;
  }

let scalar_neg_involutive (a: num)
    : Lemma (scalar_neg (scalar_neg a) == a) [SMTPat (scalar_neg (scalar_neg a))] =
  scalar_neg_unique (scalar_neg a) a

let scalar_neg_add_dist (a1 a2: num)
    : Lemma (scalar_neg (scalar_add a1 a2) == scalar_add (scalar_neg a1) (scalar_neg a2))
      [SMTPat (scalar_neg (scalar_add a1 a2))] =
  let n1 = scalar_neg a1 in
  let n2 = scalar_neg a2 in
  calc (==) {
    (scalar_add (scalar_add a1 a2) (scalar_add n1 n2) <: num);
    == { scalar_add_assoc a1 a2 (scalar_add n1 n2) }
    scalar_add a1 (scalar_add a2 (scalar_add n1 n2));
    == { scalar_add_comm n1 n2 }
    scalar_add a1 (scalar_add a2 (scalar_add n2 n1));
    == { scalar_add_assoc a2 n2 n1 }
    scalar_add a1 (scalar_add (scalar_add a2 n2) n1);
    == { }
    scalar_add a1 (scalar_add zero n1);
    == { }
    scalar_add a1 n1;
    == { }
    zero;
  };
  scalar_neg_unique (scalar_add a1 a2) (scalar_add n1 n2)

let scalar_mul_neg (a1 a2: num)
    : Lemma (scalar_mul a1 (scalar_neg a2) == scalar_neg (scalar_mul a1 a2))
      [SMTPat (scalar_mul a1 (scalar_neg a2))] =
  scalar_mul_add_dist_l a1 a2 (scalar_neg a2);
  scalar_neg_unique (scalar_mul a1 a2) (scalar_mul a1 (scalar_neg a2))

(* multiplication by a nonzero scalar is injective *)
let scalar_mul_cancel_r (x y: num) (l: num{is_nnz l})
    : Lemma (requires scalar_mul x l == scalar_mul y l) (ensures x == y) =
  let i = scalar_div one l in
  let cancel (z: num) : Lemma (scalar_mul (scalar_mul z l) i == z) =
    scalar_mul_assoc z l i;
    scalar_mul_comm l i
  in
  cancel x;
  cancel y

let scalar_mul_div_comm (a b: num) (l: num{is_nnz l})
    : Lemma (scalar_mul a (scalar_div b l) == scalar_mul (scalar_div a l) b) =
  let al = scalar_div a l in
  let bl = scalar_div b l in
  calc (==) {
    (scalar_mul a bl <: num);
    == { }
    scalar_mul (scalar_mul al l) bl;
    == { scalar_mul_assoc al l bl }
    scalar_mul al (scalar_mul l bl);
    == { scalar_mul_comm l bl }
    scalar_mul al (scalar_mul bl l);
    == { }
    scalar_mul al b;
  }

let scalar_div_assoc (a1: num) (a2: num{is_nnz a2}) (a3: num{is_nnz a3})
    : Lemma (scalar_div (scalar_div a1 a2) a3 == scalar_div a1 (scalar_mul a2 a3))
      [SMTPat (scalar_div (scalar_div a1 a2) a3)] =
  let l = scalar_mul a2 a3 in
  let lhs = scalar_div (scalar_div a1 a2) a3 in
  calc (==) {
    (scalar_mul lhs l <: num);
    == { scalar_mul_comm a2 a3 }
    scalar_mul lhs (scalar_mul a3 a2);
    == { scalar_mul_assoc lhs a3 a2 }
    scalar_mul (scalar_mul lhs a3) a2;
    == { }
    a1;
  };
  scalar_mul_cancel_r lhs (scalar_div a1 l) l

let scalar_mul_neg_l (a1 a2: num)
    : Lemma (scalar_mul (scalar_neg a1) a2 == scalar_neg (scalar_mul a1 a2)) =
  scalar_mul_comm (scalar_neg a1) a2;
  scalar_mul_comm a1 a2

let scalar_mul_swap_r (a b c: num)
    : Lemma (scalar_mul (scalar_mul a b) c == scalar_mul (scalar_mul a c) b) =
  scalar_mul_assoc a b c;
  scalar_mul_comm b c;
  scalar_mul_assoc a c b

(* (a+b)+(c+d) == (a+c)+(b+d) *)
let scalar_add_middle_swap (a b c d: num)
    : Lemma (scalar_add (scalar_add a b) (scalar_add c d) ==
             scalar_add (scalar_add a c) (scalar_add b d)) =
  calc (==) {
    (scalar_add (scalar_add a b) (scalar_add c d) <: num);
    == { scalar_add_assoc a b (scalar_add c d) }
    scalar_add a (scalar_add b (scalar_add c d));
    == { scalar_add_assoc b c d }
    scalar_add a (scalar_add (scalar_add b c) d);
    == { scalar_add_comm b c }
    scalar_add a (scalar_add (scalar_add c b) d);
    == { scalar_add_assoc c b d }
    scalar_add a (scalar_add c (scalar_add b d));
    == { scalar_add_assoc a c (scalar_add b d) }
    scalar_add (scalar_add a c) (scalar_add b d);
  }

(* subtraction *)
let scalar_sub (a1 a2: num) : num = scalar_add a1 (scalar_neg a2)

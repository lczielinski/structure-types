module StructureTypes.Scalar.Lemmas

open StructureTypes.Scalar

let scalar_mul_add_r (a b c: num)
    : Lemma (scalar_mul a (scalar_add b c) == scalar_add (scalar_mul a b) (scalar_mul a c)) =
  scalar_mul_comm a (scalar_add b c);
  scalar_mul_comm b a;
  scalar_mul_comm c a

let scalar_neg_unique (a b: num)
    : Lemma (requires scalar_add a b == scalar_zero) (ensures b == scalar_neg a) =
  calc (==) {
    (b <: num);
    == { }
    scalar_add scalar_zero b;
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

let scalar_neg_add (a1 a2: num)
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
    scalar_add a1 (scalar_add scalar_zero n1);
    == { }
    scalar_add a1 n1;
    == { }
    scalar_zero;
  };
  scalar_neg_unique (scalar_add a1 a2) (scalar_add n1 n2)

let scalar_mul_neg_r (a1 a2: num)
    : Lemma (scalar_mul a1 (scalar_neg a2) == scalar_neg (scalar_mul a1 a2))
      [SMTPat (scalar_mul a1 (scalar_neg a2))] =
  scalar_mul_add_r a1 a2 (scalar_neg a2);
  scalar_neg_unique (scalar_mul a1 a2) (scalar_mul a1 (scalar_neg a2))

let scalar_mul_cancel_r (x y: num) (l: num{scalar_is_nnz l})
    : Lemma (requires scalar_mul x l == scalar_mul y l) (ensures x == y) =
  let i = scalar_div scalar_one l in
  let cancel (z: num) : Lemma (scalar_mul (scalar_mul z l) i == z) =
    scalar_mul_assoc z l i;
    scalar_mul_comm l i
  in
  cancel x;
  cancel y

let scalar_mul_div_cancel (a: num{scalar_is_nnz a}) (b: num)
  : Lemma (scalar_mul a (scalar_div b a) == b) [SMTPat (scalar_mul a (scalar_div b a))] =
  scalar_mul_comm a (scalar_div b a)

let scalar_mul_div_comm (a b: num) (l: num{scalar_is_nnz l})
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

let scalar_div_assoc (a1: num) (a2: num{scalar_is_nnz a2}) (a3: num{scalar_is_nnz a3})
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

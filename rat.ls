
RatP: Type
RatP = Prod IntP IntP

RatP_from_ints: IntP -> IntP -> RatP
from_ints = intro IntP IntP

RatP_numerator: RatP -> IntP
numerator = fst IntP IntP

RatP_denominator: RatP -> IntP
denominator = snd IntP IntP

RatP_one: RatP
one = from_ints one one

RatP_mul: RatP -> RatP -> RatP
mul x y = from_ints \
  (mul (numerator x) (numerator y)) (mul (denominator x) (denominator y))

RatP_add: RatP -> RatP -> RatP
add x y = from_ints \
  (add \
    (mul (numerator x) (denominator y)) \
    (mul (denominator x) (numerator y))) \
  (mul (denominator x) (denominator y))

Rat: Type
Rat = Signed RatP

Rat_negative: RatP -> Rat
negative = negative RatP

-- @Completeness Signed_zero should overload fine
Rat_zero: Rat
zero = Signed_zero RatP

Rat_positive: RatP -> Rat
positive = positive RatP

Rat_negate: Rat -> Rat
negate = negate RatP

Rat_from_ints_n: IntP -> IntP -> Rat
Rat_from_ints_n x y = negative (from_ints x y)

Rat_from_ints_p: IntP -> IntP -> Rat
Rat_from_ints_p x y = positive (from_ints x y)

Rat_from_ints: Int -> IntP -> Rat
from_ints x = x (IntP -> Rat) \
  Rat_from_ints_n (const Rat zero IntP) Rat_from_ints_p

RatP_diff: RatP -> RatP -> Rat
diff x y = from_ints \
  (diff \
    (mul (numerator x) (denominator y)) \
    (mul (denominator x) (numerator y))) \
  (mul (denominator x) (denominator y))


Rat_add: Rat -> Rat -> Rat
add = Signed_add RatP add diff

Rat_mul: Rat -> Rat -> Rat
mul = Signed_mul RatP mul


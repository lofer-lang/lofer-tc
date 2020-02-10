
Signed: Type -> Type
Signed A = (M: Type) -> (A -> M) -> M -> (A -> M) -> M

Signed_negative: (A: Type) -> A -> Signed A
negative A x M n z p = n x

Signed_zero: (A: Type) -> Signed A
zero A M n z p = z

Signed_positive: (A: Type) -> A -> Signed A
positive A x M n z p = p x

Signed_negate: (A: Type) -> Signed A -> Signed A
negate A x = x (Signed A) (positive A) (zero A) (negative A)

Signed_negative_from: (A: Type) -> (A -> A -> A) -> A -> A -> Signed A
Signed_negative_from A f x y = negative A (f x y)

Signed_then_negate: (A: Type) -> (A -> A -> Signed A) -> A -> A -> Signed A
Signed_then_negate A f x y = negate A (f x y)

Signed_add_n: (A: Type) -> (A -> A -> A) -> (A -> A -> Signed A) -> \
  A -> Signed A -> Signed A
Signed_add_n A f g x y = y (Signed A) \
  (Signed_negative_from A f x) (negative A x) (Signed_then_negate A g x)

Signed_positive_from: (A: Type) -> (A -> A -> A) -> A -> A -> Signed A
Signed_positive_from A f x y = positive A (f x y)

Signed_add_p: (A: Type) -> (A -> A -> A) -> (A -> A -> Signed A) -> \
  A -> Signed A -> Signed A
Signed_add_p A f g x y = y (Signed A) \
  (g x) (positive A x) (Signed_positive_from A f x)

Signed_add: (A: Type) -> (A -> A -> A) -> (A -> A -> Signed A) -> \
  Signed A -> Signed A -> Signed A
Signed_add A f g x = x (Signed A -> Signed A) \
  (Signed_add_n A f g) (id (Signed A)) (Signed_add_p A f g)


Signed_mul_n: (A: Type) -> (A -> A -> A) -> A -> Signed A -> Signed A
Signed_mul_n A f x y = y (Signed A) \
  (Signed_positive_from A f x) (zero A) (Signed_negative_from A f x)

Signed_mul_p: (A: Type) -> (A -> A -> A) -> A -> Signed A -> Signed A
Signed_mul_p A f x y = y (Signed A) \
  (Signed_negative_from A f x) (zero A) (Signed_positive_from A f x)

Signed_mul: (A: Type) -> (A -> A -> A) -> Signed A -> Signed A -> Signed A
Signed_mul A f x = x (Signed A -> Signed A) \
  (Signed_mul_n A f) (const (Signed A) (zero A) (Signed A)) (Signed_mul_p A f)


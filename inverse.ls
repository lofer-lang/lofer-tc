
Eq: (A: Type) -> A -> A -> Type
Eq A x y = (C: A -> Type) -> C x -> C y

refl: (A: Type) -> (x: A) -> Eq A x x
refl A x C cx = cx

trans: (A: Type) -> (x: A) -> (y: A) -> (z: A) -> \
  Eq A x y -> Eq A y z -> Eq A x z
trans A x y z xy yz = yz (Eq A x) xy

cong_Motive: (A: Type) -> (B: Type) -> (A -> B) -> (B -> Type) -> \
  A -> Type
cong_Motive A B f C x = C (f x)

cong: (A: Type) -> (B: Type) -> (f: A -> B) -> (x: A) -> (y: A) -> \
  Eq A x y -> Eq B (f x) (f y)
cong A B f x y p C = p (cong_Motive A B f C)

sym_Motive: (A: Type) -> (x: A) -> (A -> Type) -> A -> Type
sym_Motive A x C y = C y -> C x

sym: (A: Type) -> (x: A) -> (y: A) -> Eq A x y -> Eq A y x
sym A x y p C = p (sym_Motive A x C) (id (C x))

LeftInverse: (A: Type) -> (B: Type) -> (f: A -> B) -> (g: B -> A) -> Type
LeftInverse A B f g = (x: A) -> Eq A (g (f (x))) x

inverses_unique: (A: Type) -> (B: Type) -> (f: A -> B) -> (l: B -> A) -> \
  (r: B -> A) -> LeftInverse A B f l -> LeftInverse B A r f -> \
  (y: B) -> Eq A (l y) (r y)
inverses_unique A B f l r li ri y = trans A (l y) (l (f (r y))) (r y) \
  (cong B A l y (f (r y)) (sym B (f (r y)) y (ri y))) \
  (li (r y))


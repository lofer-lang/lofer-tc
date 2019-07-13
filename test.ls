
id: (A: Type) -> A -> A
id _ x = x

const: (A: Type) -> (B: Type) -> A -> B -> A
const _ _ x _ = x

leak: (A: Type) -> (B: Type) -> A -> B -> B
leak _ _ _ x = x

discard: (A: Type) -> (B: Type) -> A -> B -> B
discard _ B _ = id B

compose: (A: Type) -> (B: Type) -> (C: Type) -> (B -> C) -> (A -> B) -> A -> C
compose _ _ _ f g x = f (g x)

s: (A: Type) -> (B: A -> Type) -> (C: (x: A) -> B x -> Type) ->\
  ((x: A) -> (y: B x) -> C x y) -> (g: (x: A) -> B x) -> (x: A) -> C x (g x)
s _ _ _ f g x = f x (g x)

shadowBug: (A: Type) -> (C: Type -> Type) -> C (A -> A) -> A -> C (A -> A)
shadowBug A C x _ = x

Pi: (A: Type) -> (B: A -> Type) -> Type
Pi A B = (x: A) -> B x

s': (A: Type) -> (B: A -> Type) -> (C: (x: A) -> B x -> Type) ->\
  ((x: A) -> (y: B x) -> C x y) -> (g: (x: A) -> B x) -> (x: A) -> C x (g x)
s' = s

Id: (A: Type) -> A -> A -> Type
Id A x y = (C: A -> A -> Type) -> (refl: (x': A) -> C x' x') -> C x y

refl: (A: Type) -> (x: A) -> Id A x x
refl A x C refl' = refl' x

idEval: (A: Type) -> (x: A) -> Id A x (id A x)
idEval = refl

Bool: Type
Bool = (A: Type) -> A -> A -> A

true: Bool
true A x y = x

false: Bool
false A x y = y

true': Bool
true' A = const A A

false': Bool
false' A = const (A -> A) A (id A)




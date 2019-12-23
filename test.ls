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
true' A x = const A x A

false': Bool
false' A = const (A -> A) (id A) A


From: Type -> Type -> Type
From A T = A -> T

OutputFamily: Type -> Type
OutputFamily A = (F: Type -> Type) -> F A -> F A

mkOutputFamily: (A: Type) -> OutputFamily A
mkOutputFamily A F x = x

arrowOutputBug1: (A: Type) -> (B: Type) -> (A -> B) -> A -> B
arrowOutputBug1 A B f x = \
  mkOutputFamily B (From A) f x

arrowOutputBug2: (A: Type) -> (B: Type) -> (A -> B) -> A -> B
arrowOutputBug2 A B f x = \
  mkOutputFamily B OutputFamily (mkOutputFamily B) (From A) f x


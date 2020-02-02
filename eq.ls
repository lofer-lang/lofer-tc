
Eq: (A: Type) -> A -> A -> Type
Eq A x y = (C: A -> Type) -> C x -> C y

refl: (A: Type) -> (x: A) -> Eq A x x
refl A x C m = m


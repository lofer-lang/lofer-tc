
id: (A: Type) -> A -> A
id _ x = x

const: (A: Type) -> (B: Type) -> A -> B -> A
const _ _ x _ = x

leak: (A: Type) -> (B: Type) -> A -> B -> B
leak _ _ _ x = x

compose: (A: Type) -> (B: Type) -> (C: Type) -> (B -> C) -> (A -> B) -> A -> C
compose _ _ _ f g x = f (g x)



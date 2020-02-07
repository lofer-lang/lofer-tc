
Neg: Type -> Type
Neg A = A -> Void

-- special case of exp_coma
Neg_comap: (A: Type) -> (B: Type) -> (A -> B) -> Neg B -> Neg A
comap A B f ny x = ny (f x)

-- flip A B Void
contrapositive: (A: Type) -> (B: Type) -> (A -> Neg B) -> B -> Neg A
contrapositive A B f y x = f x y

Neg_cases: (A: Type) -> (B: Type) -> (A -> Neg B) -> (Neg A -> Neg B) -> Neg B
cases A B yes no b = no (contrapositive A B yes b) b

Irref: Type -> Type
Irref A = Neg (Neg A)

Irref_cases: (A: Type) -> (B: Type) -> (A -> B) -> (Neg A -> B) -> Irref B
cases A B yes no nb = Neg_comap (Neg A) B no nb (Neg_comap A B yes nb)

Stab: Type -> Type
Stab A = Irref A -> A



Neg: Type -> Type
Neg A = A -> Void

-- special case of exp_coma
neg_comap: (A: Type) -> (B: Type) -> (A -> B) -> Neg B -> Neg A
neg_comap A B f ny x = ny (f x)

-- flip A B Void
contrapositive: (A: Type) -> (B: Type) -> (A -> Neg B) -> B -> Neg A
contrapositive A B f y x = f x y

Irref: Type -> Type
Irref A = Neg (Neg A)

irref_map: (A: Type) -> (B: Type) -> (A -> B) -> Irref A -> Irref B
irref_map A B f = neg_comap (Neg B) (Neg A) (neg_comap A B f)

irref_pure: (A: Type) -> A -> Irref A
irref_pure A x nx = nx x

Stab: Type -> Type
Stab A = Irref A -> A

neg_stab: (A: Type) -> Stab (Neg A)
neg_stab A nnnx x = nnnx (irref_pure A x)

-- you could call this irref_stab as well, but monads are more useful
irref_join: (A: Type) -> Irref (Irref A) -> Irref A
irref_join A = neg_stab (Neg A)

Dec: Type -> Type
Dec A = (M: Type) -> (A -> M) -> (Neg A -> M) -> M

yes: (A: Type) -> A -> Dec A
yes A x M yc nc = yc x

no: (A: Type) -> Neg A -> Dec A
no A nx M yc nc = nc nx

ndec_implies_n: (A: Type) -> Neg (Dec A) -> Neg A
ndec_implies_n A ndec x = ndec (yes A x)

excluded_middle: (A: Type) -> Irref (Dec A)
excluded_middle A ndec = ndec (no A (ndec_implies_n A ndec))

dec_lemma: (A: Type) -> (B: Type) -> (Dec A -> Neg B) -> Neg B
dec_lemma A B f b = excluded_middle A (contrapositive (Dec A) B f b)


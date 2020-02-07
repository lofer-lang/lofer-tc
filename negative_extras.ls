
Irref_map: (A: Type) -> (B: Type) -> (A -> B) -> Irref A -> Irref B
map A B f = Neg_comap (Neg B) (Neg A) (Neg_comap A B f)

Irref_pure: (A: Type) -> A -> Irref A
pure A x nx = nx x

Neg_stab: (A: Type) -> Stab (Neg A)
stab A nnnx x = nnnx (Irref_pure A x)

-- you could call this Irref_stab as well, but monads are more useful
Irref_join: (A: Type) -> Irref (Irref A) -> Irref A
join A = Neg_stab (Neg A)

Dec: Type -> Type
Dec A = (M: Type) -> (A -> M) -> (Neg A -> M) -> M

yes: (A: Type) -> A -> Dec A
yes A x M yc nc = yc x

no: (A: Type) -> Neg A -> Dec A
no A nx M yc nc = nc nx

excluded_middle: (A: Type) -> Irref (Dec A)
excluded_middle A = cases A (Dec A) (yes A) (no A)

Dec_lemma: (A: Type) -> (B: Type) -> (Dec A -> Neg B) -> Neg B
Dec_lemma A B f b = excluded_middle A (contrapositive (Dec A) B f b)


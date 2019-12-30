
-- Void

postulate Void_Fam: Void -> Type
Void_Fam = Void_case Type

Void_elim: (M: Void -> Type) -> (x: Void) -> M x
Void_elim M x = x (M x)

-- Unit

Unit_case: (A: Type) -> A -> Unit -> A
Unit_case A x f = f A x

postulate Unit_Fam: Type -> Unit -> Type
Unit_Fam = Unit_case Type

postulate Unit_elim: (M: Unit -> Type) -> M id -> (x: Unit) -> M x
Unit_elim M m x = x (M x) m

-- Bool

Bool: Type
Bool = (A: Type) -> A -> A -> A

true: Bool
true A x y = x

false: Bool
false A x y = y

Bool_case: (A: Type) -> A -> A -> Bool -> A
Bool_case A x y f = f A x y

postulate Bool_Fam: Type -> Type -> Bool -> Type
Bool_Fam T U x = x Type T U

postulate Bool_elim: (M: Bool -> Type) -> M true -> M false -> (x: Bool) -> M x
Bool_elim M mt mf x = x (M x) mt mf

-- Maybe

Maybe: Type -> Type
Maybe A = (C: Type) -> C -> (A -> C) -> C

nothing: (A: Type) -> Maybe A
nothing A C fl fr = fl

just: (A: Type) -> A -> Maybe A
just A x C fl fr = fr x

Maybe_case: (A: Type) -> (C: Type) -> C -> (A -> C) -> \
  Maybe A -> C
Maybe_case A C fl fr x = x C fl fr

postulate Maybe_Fam: (A: Type) -> Type -> (A -> Type) -> \
  Maybe A -> Type
Maybe_Fam A = Maybe_case A Type

postulate Maybe_elim: (A: Type) -> (M: Maybe A -> Type) -> \
  M (nothing A) -> ((x: A) -> M (just A x)) -> \
  (x: Maybe A) -> M x
Maybe_elim A B M ml mr x = x (M x) ml mr

-- Sum

Sum: Type -> Type -> Type
Sum A B = (C: Type) -> (A -> C) -> (B -> C) -> C

inl: (A: Type) -> (B: Type) -> A -> Sum A B
inl A B x C fl fr = fl x

inr: (A: Type) -> (B: Type) -> B -> Sum A B
inr A B y C fl fr = fr y

Sum_case: (A: Type) -> (B: Type) -> (C: Type) -> (A -> C) -> (B -> C) -> \
  Sum A B -> C
Sum_case A B C fl fr x = x C fl fr

postulate Sum_Fam: (A: Type) -> (B: Type) -> (A -> Type) -> (B -> Type) -> \
  Sum A B -> Type
Sum_Fam A B = Sum_case A B Type

postulate Sum_elim: (A: Type) -> (B: Type) -> (M: Sum A B -> Type) -> \
  ((x: A) -> M (inl A B x)) -> ((y: B) -> M (inr A B y)) -> \
  (x: Sum A B) -> M x
Sum_elim A B M ml mr x = x (M x) ml mr

-- Prod

-- while writing this I kept writing Pair instead of Prod...
-- Pair is probably a better name? but Prod distinguishes it from Sigma
Prod: Type -> Type -> Type
Prod A B = (C: Type) -> (A -> B -> C) -> C

Prod_intro: (A: Type) -> (B: Type) -> A -> B -> Prod A B
Prod_intro A B x y C f = f x y

Prod_case: (A: Type) -> (B: Type) -> (C: Type) -> (A -> B -> C) -> \
  Prod A B -> C
Prod_case A B C f x = x C f

postulate Prod_Fam: (A: Type) -> (B: Type) -> (A -> B -> Type) -> \
  Prod A B -> Type
Prod_Fam A B = Prod_case A B Type

postulate Prod_elim: (A: Type) -> (B: Type) -> (M: Prod A B -> Type) -> \
  ((x: A) -> (y: B) -> M (Prod_intro A B x y)) -> \
  (x: Prod A B) -> M x
Prod_elim A B M m x = x (M x) m

Prod_fst_method: (A: Type) -> (B: Type) -> A -> B -> A
Prod_fst_method A B x y = x

Prod_fst: (A: Type) -> (B: Type) -> Prod A B -> A
Prod_fst A B p = p A (Prod_fst_method A B)

Prod_snd_method: (A: Type) -> (B: Type) -> A -> B -> B
Prod_snd_method A B x y = y

Prod_snd: (A: Type) -> (B: Type) -> Prod A B -> B
Prod_snd A B p = p B (Prod_snd_method A B)

-- Sigma

Sigma: (A: Type) -> (A -> Type) -> Type
Sigma A B = (C: Type) -> ((x: A) -> B x -> C) -> C

Sigma_intro: (A: Type) -> (B: A -> Type) -> (x: A) -> B x -> Sigma A B
Sigma_intro A B x y C f = f x y

Sigma_case: (A: Type) -> (B: A -> Type) -> (C: Type) -> ((x: A) -> B x -> C) -> \
  Sigma A B -> C
Sigma_case A B C f x = x C f

postulate Sigma_Fam: (A: Type) -> (B: A -> Type) -> ((x: A) -> B x -> Type) -> \
  Sigma A B -> Type
Sigma_Fam A B = Sigma_case A B Type

postulate Sigma_elim: (A: Type) -> (B: A -> Type) -> (M: Sigma A B -> Type) -> \
  ((x: A) -> (y: B x) -> M (Sigma_intro A B x y)) -> \
  (x: Sigma A B) -> M x
Sigma_elim A B M m x = x (M x) m

Sigma_fst_method: (A: Type) -> (B: A -> Type) -> (x: A) -> B x -> A
Sigma_fst_method A B x y = x

Sigma_fst: (A: Type) -> (B: A -> Type) -> Sigma A B -> A
Sigma_fst A B p = p A (Sigma_fst_method A B)

Sigma_snd_Motive: (A: Type) -> (B: A -> Type) -> Sigma A B -> Type
Sigma_snd_Motive A B x = B (Sigma_fst A B x)

Sigma_snd_method: (A: Type) -> (B: A -> Type) -> (x: A) -> B x -> B x
Sigma_snd_method A B x y = y

Sigma_snd: (A: Type) -> (B: A -> Type) -> (x: Sigma A B) -> B (Sigma_fst A B x)
Sigma_snd A B = Sigma_elim A B (Sigma_snd_Motive A B) (Sigma_snd_method A B)



Type: U1
Type = U0

Void: Type
Void = (A: Type) -> A
void_fold: (A: Type) -> Void -> A
void_fold A x = x A

Unit: Type
Unit = (A: Type) -> A -> A
id: Unit
id A x = x

const: (A: Type) -> A -> (B: Type) -> B -> A
const A x B y = x

Paradoxical: (Type -> Type) -> Type
Paradoxical F = (A: Type) -> (F A -> A) -> (A -> F A) -> Void

Neg: Type -> Type
Neg A = A -> Void

self_apply: (A: Type) -> (A -> A -> Void) -> A -> Void
self_apply A open x = open x x

currys_paradox: Paradoxical Neg
currys_paradox A close open = self_apply A open (close (self_apply A open))

Mappable: (Type -> Type) -> Type
Mappable F = (A: Type) -> (B: Type) -> (A -> B) -> F A -> F B

empty_case: (F: Type -> Type) -> Neg (F Void) -> Neg (Paradoxical F)
empty_case F nfv para = para Void nfv (void_fold (F Void))

nonempty_case: (F: Type -> Type) -> Mappable F -> F Void -> Neg (Paradoxical F)
nonempty_case F map fv npara = npara Unit \
  (const Unit id (F Unit)) \
  (const (F Unit) (map Void Unit (void_fold Unit) fv) Unit)

Dec: Type -> Type
Dec A = (M: Type) -> (A -> M) -> (Neg A -> M) -> M

combine_cases: (F: Type -> Type) -> \
  Mappable F -> Dec (F Void) -> Neg (Paradoxical F)
combine_cases F map dec = \
  dec (Neg (Paradoxical F)) (nonempty_case F map) (empty_case F)

yes: (A: Type) -> A -> Dec A
yes A x M yc nc = yc x

no: (A: Type) -> Neg A -> Dec A
no A nx M yc nc = nc nx

ndec_implies_n: (A: Type) -> Neg (Dec A) -> Neg A
ndec_implies_n A ndec x = ndec (yes A x)

excluded_middle: (A: Type) -> Neg (Neg (Dec A))
excluded_middle A ndec = ndec (no A (ndec_implies_n A ndec))

contrapositive: (A: Type) -> (B: Type) -> (Dec A -> Neg B) -> B -> Neg (Dec A)
contrapositive A B f b dec = f dec b

dec_lemma: (A: Type) -> (B: Type) -> (Dec A -> Neg B) -> Neg B
dec_lemma A B f b = excluded_middle A (contrapositive A B f b)

inductive_safety_theorem: (F: Type -> Type) -> \
  Mappable F -> Neg (Paradoxical F)
inductive_safety_theorem F map = \
  dec_lemma (F Void) (Paradoxical F) (combine_cases F map)


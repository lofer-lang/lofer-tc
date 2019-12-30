
Paradoxical: (Type -> Type) -> Type
Paradoxical F = (A: Type) -> (F A -> A) -> (A -> F A) -> Void

self_apply: (A: Type) -> (A -> A -> Void) -> A -> Void
self_apply A open x = open x x

currys_paradox: Paradoxical Neg
currys_paradox A close open = self_apply A open (close (self_apply A open))

Mappable: (Type -> Type) -> Type
Mappable F = (A: Type) -> (B: Type) -> (A -> B) -> F A -> F B

empty_case: (F: Type -> Type) -> Neg (F Void) -> Neg (Paradoxical F)
empty_case F nfv para = para Void nfv (Void_case (F Void))

nonempty_case: (F: Type -> Type) -> Mappable F -> F Void -> Neg (Paradoxical F)
nonempty_case F map fv npara = npara Unit \
  (const Unit id (F Unit)) \
  (const (F Unit) (map Void Unit (Void_case Unit) fv) Unit)

inductive_safety_theorem: (F: Type -> Type) -> \
  Mappable F -> Neg (Paradoxical F)
inductive_safety_theorem F map = \
  Neg_cases (F Void) (Paradoxical F) (nonempty_case F map) (empty_case F)


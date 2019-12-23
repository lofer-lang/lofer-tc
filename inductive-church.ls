Ind: (Type -> Type) -> Type
Ind F = (M: Type) -> (F M -> M) -> M

ind_fold: (F: Type -> Type) -> (M: Type) -> (F M -> M) -> Ind F -> M
ind_fold F M m x = x M m

Mappable: (Type -> Type) -> Type
Mappable F = (A: Type) -> (B: Type) -> (A -> B) -> F A -> F B

-- these operations have O(n) complexity, but the Ind postulates are no-op
Closable: (Type -> Type) -> Type
Closable F = F (Ind F) -> Ind F
close: (F: Type -> Type) -> Mappable F -> Closable F
close F map x M m = m (map (Ind F) M (ind_fold F M m) x)

Openable: (Type -> Type) -> Type
Openable F = Ind F -> F (Ind F)
open: (F: Type -> Type) -> Mappable F -> Openable F
open F map x = x (F (Ind F)) (map (F (Ind F)) (Ind F) (close F map))


Into: Type -> Type -> Type
Into A T = T -> A

self_apply: (A: Type) -> Openable (Into A) -> Into A (Ind (Into A))
self_apply A open x = open x x

currys_paradox: (A: Type) -> Openable (Into A) -> Closable (Into A) -> A
currys_paradox A open close = self_apply A open (close (self_apply A open))

IntoMethod: Type -> Type -> Type
IntoMethod A M = (M -> A) -> M

method_implies_nn: (M: Type) -> IntoMethod Void M -> (M -> Void) -> Void
method_implies_nn M m nm = nm (m nm)

stab_implies_fold: (M: Type) -> (((M -> Void) -> Void) -> M) -> ((M -> Void) -> M) -> M
stab_implies_fold M stab m = stab (method_implies_nn M m)

-- does this mean Ind (Into Void) is irrefutable?
-- hence not openable, since A->~A -> (~~A)->~A -> ~A -> Void
build_ind0: ((A: Type) -> ((A -> Void) -> Void) -> A) -> Ind (Into Void)
build_ind0 stab M m = stab M (method_implies_nn M m)

build_ind1: Ind (Into Unit)
build_ind1 M m = m (const Unit id M)

fill_method: (A: Type) -> (M: Type) -> M -> IntoMethod A M
fill_method A M x f = x

open_into_unit: Openable (Into Unit)
open_into_unit x y = id

close_into_unit: Closable (Into Unit)
close_into_unit x = build_ind1



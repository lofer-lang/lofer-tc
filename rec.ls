---------------------
-- recursive types

-- we require mappable so that curry's paradox doesn't typecheck
-- could move this definition to a functor.ls file
Mappable: (Type -> Type) -> Type
Mappable F = (A: Type) -> (B: Type) -> (A -> B) -> F A -> F B

postulate Rec: (F: Type -> Type) -> Type
postulate Rec_close: (F: Type -> Type) -> Mappable F -> \
  F (Rec F) -> Rec F
close F map x = x
postulate Rec_open: (F: Type -> Type) -> Mappable F -> \
  Rec F -> F (Rec F)
open F map x = x

Into: Type -> Type -> Type
Into A T = T -> A

self_apply: (A: Type) -> (map: Mappable (Into (Unit -> A))) -> ((Unit -> A) -> A) -> \
  Rec (Into (Unit -> A)) -> Unit -> A
self_apply A map f x _ = f (Rec_open (Into (Unit -> A)) map x x)

-- note fix does not actually use the map function
fix: (A: Type) -> (map: Mappable (Into (Unit -> A))) -> ((Unit -> A) -> A) -> A
fix A map f = self_apply A map f (Rec_close (Into (Unit -> A)) map (self_apply A map f)) id

-- currys_paradox: Mappable (Into (Unit -> Void)) -> Void
-- currys_paradox map = fix Void map (\x -> x id)

-- Mappable (Into Void) was already absurd!
-- currys_paradox_redundant: Mappable (Into Void) -> Void
-- currys_paradox_redundant map = map Void Unit (const Unit id Void) (id Void) id

Rec_fold_step: (F: Type -> Type) -> (map: Mappable F) -> \
  (A: Type) -> (F A -> A) -> (Unit -> Rec F -> A) -> Rec F -> A
Rec_fold_step F map A m prev x = m (map (Rec F) A (prev id) (Rec_open F map x))

postulate Rec_fold: (F: Type -> Type) -> (map: Mappable F) -> \
  (A: Type) -> (F A -> A) -> Rec F -> A
fold F map A m = fix (Rec F -> A) id (Rec_fold_step F map A m)


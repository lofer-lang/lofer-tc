Type: U1
Type = U0

Void: Type
Void = (A: Type) -> A
Neg: Type -> Type
Neg A = A -> Void

Unit: Type
Unit = (A: Type) -> A -> A
id: Unit
id A x = x

---------------------
-- inductive types

Mappable: (Type -> Type) -> Type
Mappable F = (A: Type) -> (B: Type) -> (A -> B) -> F A -> F B

-- inductive data types are fixpoints of functors!
postulate Ind: (F: Type -> Type) -> Mappable F -> Type
postulate ind_close: (F: Type -> Type) -> (map: Mappable F) -> \
  F (Ind F map) -> Ind F map
ind_close F map x = x
postulate ind_open: (F: Type -> Type) -> (map: Mappable F) -> \
  Ind F map -> F (Ind F map)
ind_open F map x = x


Into: Type -> Type -> Type
Into A T = T -> A

helper: (A: Type) -> (map: Mappable (Into A)) -> \
  Ind (Into A) map -> Ind (Into A) map -> A
helper A = ind_open (Into A)
self_apply: (A: Type) -> (map: Mappable (Into A)) -> (A -> A) -> \
  Ind (Into A) map -> A
self_apply A map f x = f (helper A map x x)
TODO = f (ind_open (Into A) map x x)

-- note fix does not actually use the map function
fix: (A: Type) -> (map: Mappable (Into A)) -> (A -> A) -> A
fix A map f = self_apply A map f (ind_close (Into A) map (self_apply A map f))

currys_paradox: Neg (Mappable (Into Void))
currys_paradox map = fix Void map (id Void)

-- Mappable (Into Void) was already absurd!
map_void: Neg (Mappable (Into Void))
map_void map = map Void Unit (id Void) id
TODO = type checking during above definition is bugged for some reason

ind_fold_step: (F: Type -> Type) -> (map: Mappable F) -> \
  (A: Type) -> (F A -> A) -> (Ind F map -> A) -> Ind F map -> A
ind_fold_step F map A m prev x = m (map (Ind F map) A prev (ind_open F map x))

postulate ind_fold: (F: Type -> Type) -> (map: Mappable F) -> \
  (A: Type) -> (F A -> A) -> Ind F map -> A
ind_fold F map A m = fix (Ind F map -> A) id (ind_fold_step F map A m)

---------------------
-- natural numbers

Maybe: Type -> Type
Maybe A = (M: Type) -> (A -> M) -> M -> M

nothing : (A: Type) -> Maybe A
nothing A M f y = y

just: (A: Type) -> A -> Maybe A
just A x M f y = f x

maybe_fold: (A: Type) -> (M: Type) -> (A -> M) -> M -> Maybe A -> M
maybe_fold A M f y mx = mx M f y

thenJust: (A: Type) -> (B: Type) -> (A -> B) -> A -> Maybe B
thenJust A B f x = just B (f x)

maybe_map: Mappable Maybe
maybe_map A B f mx = mx (Maybe B) (thenJust A B f) (nothing B)

Nat: Type
Nat = Ind Maybe maybe_map

zero: Nat
zero = ind_close Maybe maybe_map (nothing Nat)

suc: Nat -> Nat
suc x = ind_close Maybe maybe_map (just Nat x)

pred: Nat -> Maybe Nat
pred = ind_open Maybe maybe_map

nat_fold: (M: Type) -> (M -> M) -> M -> Nat -> M
nat_fold M f x = ind_fold Maybe maybe_map M (maybe_fold M M f x)


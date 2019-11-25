-- The first prototype of lofer had 4 type connectives built in, (Void, Unit,
-- Bool, Sigma) which could then be used to build larger ADTs.
-- In this file we postulate those built-ins, and build larger ADTs as before,
-- demonstrating that the current postulate system makes those builtins
-- redundant.
-- this file also demonstrates (what was) a new alternative to a full fixpoint
-- operator, which is the fixpoint type constructor paired with intro and elim
-- rules. (in the first prototype you'd literally apply fix to a type
-- constructor, which made type checking complicated, to the point where I
-- stopped maintaining type checking altogether)
-- both of these techniques have become outdated due to more novel techniques I
-- have discovered in the last week, but I am continuing to maintain this file
-- for sentimental reasons. - Jarvis, 2019-11-25
Type : U1
Type = U0

postulate Void: Type
postulate void_elim: (A: Type) -> Void -> A

postulate Unit: Type
postulate tt: Unit
postulate unit_elim: (C: Unit -> Type) -> C tt -> (x: Unit) -> C x
unit_elim C m x = m

postulate Bool: Type
postulate true: Bool
true x y = x
postulate false: Bool
false x y = y
postulate bool_elim: (C: Bool -> Type) -> C true -> C false -> (x: Bool) -> C x
bool_elim C mt mf x = x mt mf
postulate BoolFamily: Type -> Type -> Bool -> Type
BoolFamily A B x = x A B

postulate Sigma: (A: Type) -> (A -> Type) -> Type
postulate pair: (A: Type) -> (B: A -> Type) -> (x: A) -> B x -> Sigma A B
pair A B x y m = m x y
postulate uncurry: (A: Type) -> (B: A -> Type) -> (C: Sigma A B -> Type) -> \
  ((x: A) -> (y: B x) -> C (pair A B x y)) -> (p: Sigma A B) -> C p
uncurry A B C m p = p m

fstCurr: (A: Type) -> (B: A -> Type) -> (x: A) -> B x -> A
fstCurr A B x y = x
FstM: (A: Type) -> (B: A -> Type) -> Sigma A B -> Type
FstM A B p = A
fst: (A: Type) -> (B: A -> Type) -> Sigma A B -> A
fst A B = uncurry A B (FstM A B) (fstCurr A B)

-- only type checks because of uncurry depending on the pair constructor
sndCurr: (A: Type) -> (B: A -> Type) -> (x: A) -> B x -> B x
sndCurr A B x y = y
SndM: (A: Type) -> (B: A -> Type) -> Sigma A B -> Type
SndM A B p = B (fst A B p)
snd: (A: Type) -> (B: A -> Type) -> (p: Sigma A B) -> B (fst A B p)
snd A B = uncurry A B (SndM A B) (sndCurr A B)

-- church encoding this would be fine for the proofs below,
-- but J with proper dependence on the refl constructor is nice
postulate Id: (A: Type) -> A -> A -> Type
postulate refl: (A: Type) -> (x: A) -> Id A x x
refl A x refl' = refl' x
postulate J: (A: Type) -> (C: (x: A) -> (y: A) -> Id A x y -> Type) -> \
  (m: (x: A) -> C x x (refl A x)) -> (x: A) -> (y: A) -> (p: Id A x y) -> C x y p
J A C m x y p = p m
-- one could easily assume K if not introducing other Id postulates
-- such as univalence, although even with extensionality you might not want K

computett: (C: Unit -> Type) -> (m: C tt) -> \
  Id (C tt) (unit_elim C m tt) m
computett C m = refl (C tt) m

computetrue: (C: Bool -> Type) -> (mt: C true) -> (mf: C false) -> \
  Id (C true) (bool_elim C mt mf true) mt
computetrue C mt mf = refl (C true) mt
computefalse: (C: Bool -> Type) -> (mt: C true) -> (mf: C false) -> \
  Id (C false) (bool_elim C mt mf false) mf
computefalse C mt mf = refl (C false) mf

computepair: (A: Type) -> (B: A -> Type) -> (C: Sigma A B -> Type) -> \
  (m: (x: A) -> (y: B x) -> C (pair A B x y)) -> (x: A) -> (y: B x) -> \
  Id (C (pair A B x y)) (uncurry A B C m (pair A B x y)) (m x y)
computepair A B C m x y = refl (C (pair A B x y)) (m x y)
computefst: (A: Type) -> (B: A -> Type) -> (x: A) -> (y: B x) -> \
  Id A (fst A B (pair A B x y)) x
computefst A B x y = refl A x
computesnd: (A: Type) -> (B: A -> Type) -> (x: A) -> (y: B x) -> \
  Id (B x) (snd A B (pair A B x y)) y
computesnd A B x y = refl (B x) y


postulate Fix: (F: Type -> Type) -> Type
postulate fopen: (F: Type -> Type) -> Fix F -> F (Fix F)
fopen F x = x
postulate fclose: (F: Type -> Type) -> F (Fix F) -> Fix F
fclose F x = x

MaybeFam: (A: Type) -> Bool -> Type
MaybeFam A = BoolFamily A Unit
Maybe: Type -> Type
Maybe A = Sigma Bool (MaybeFam A)
nothing: (A: Type) -> Maybe A
nothing A = pair Bool (MaybeFam A) false tt
just: (A: Type) -> A -> Maybe A
just A = pair Bool (MaybeFam A) true

Nat: Type
Nat = Fix Maybe
zero: Nat
zero = fclose Maybe (nothing Nat)
suc: Nat -> Nat
suc n = fclose Maybe (just Nat n)
pred: Nat -> Maybe Nat
pred = fopen Maybe

computepred: (n: Nat) -> Id (Maybe Nat) (pred (suc n)) (just Nat n)
computepred n = refl (Maybe Nat) (just Nat n)


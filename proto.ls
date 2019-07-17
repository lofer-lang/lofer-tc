
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

sndCurr: (A: Type) -> (B: A -> Type) -> (x: A) -> B x -> B x
sndCurr A B x y = y
SndM: (A: Type) -> (B: A -> Type) -> Sigma A B -> Type
SndM A B p = B (fst A B p)
snd: (A: Type) -> (B: A -> Type) -> (p: Sigma A B) -> B (fst A B p)
snd A B = uncurry A B (SndM A B) (sndCurr A B)

postulate Id: (A: Type) -> A -> A -> Type
postulate refl: (A: Type) -> (x: A) -> Id A x x
refl A x refl' = refl' x
postulate J: (A: Type) -> (C: (x: A) -> (y: A) -> Id A x y -> Type) -> \
  (m: (x: A) -> C x x (refl A x)) -> (x: A) -> (y: A) -> (p: Id A x y) -> C x y p
J A C m x y p = p m

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


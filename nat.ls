postulate Unknown: Type

postulate Unit: Type

postulate tt: Unit

postulate unit_elim: (C: Unit -> Type) -> C tt -> (x: Unit) -> C x
unit_elim C m x = m


Bool: Type
Bool = Unknown -> Unknown -> Unknown

true: Bool
true x y = x

false: Bool
false x y = y

postulate bool_elim: (C: Bool -> Type) -> C true -> C false -> (x: Bool) -> C x
bool_elim C mt mf x = x mt mf

Nat: Type
Nat = ((Unit -> Unknown) -> Unknown) -> Unknown -> Unit -> Unknown

zero: Nat
zero f x _ = x

suc: Nat -> Nat
suc n f x _ = f (n f x)

postulate natFold: (A: Type) -> ((Unit -> A) -> A) -> A -> Nat -> A
natFold A ind base n = n ind base tt

NatSigma: (C: Nat -> Type) -> Type
NatSigma C = (D: Type) -> ((n: Nat) -> C n -> D) -> D

natpair: (C: Nat -> Type) -> (n: Nat) -> C n -> NatSigma C
natpair C n y D f = f n y

natfstCur: (C: Nat -> Type) -> (n: Nat) -> C n -> Nat
natfstCur C n y = n

natfst: (C: Nat -> Type) -> NatSigma C -> Nat
natfst C p = p Nat (natfstCur C)

natsndCur: (C: Nat -> Type) -> (n: Nat) -> C n -> C n
natsndCur C n y = y

postulate natsnd: (C: Nat -> Type) -> (p: NatSigma C) -> C (natfst C p)
natsnd C p = p (C (natfst C p)) (natsndCur C)

nat_elim_step_cur: (C: Nat -> Type) -> ((k: Nat) -> (Unit -> C k) -> C (suc k)) -> \
  (k: Nat) -> C k -> NatSigma C
nat_elim_step_cur C ind k y = natpair C (suc k) (ind k y)

nat_elim_step: (C: Nat -> Type) -> ((k: Nat) -> (Unit -> C k) -> C (suc k)) -> \
  (Unit -> NatSigma C) -> NatSigma C
nat_elim_step C ind kp = kp tt (NatSigma C) (nat_elim_step_cur C ind)

nat_elim_pair: (C: Nat -> Type) -> \
  C zero -> ((k: Nat) -> (Unit -> C k) -> C (suc k)) -> (x: Nat) -> NatSigma C
nat_elim_pair C base ind = natFold (NatSigma C) (nat_elim_step C ind) (natpair zero base)

postulate nat_elim': (C: Nat -> Type) -> \
  C zero -> ((k: Nat) -> (Unit -> C k) -> C (suc k)) -> (x: Nat) -> C x
nat_elim' C base ind x = natsnd (nat_elim_pair C base ind x)


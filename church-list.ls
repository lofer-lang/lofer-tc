
List: Type -> Type
List A = (M: Type) -> M -> (A -> M -> M) -> M

empty: (A: Type) -> List A
empty A M mb mf = mb

consl: (A: Type) -> A -> List A -> List A
consl A x xs M mb mf = mf x (xs M mb mf)

-- recursive definitions like `List A = Maybe (Pair A (List A))`
-- have foldl and foldr but only one cons
-- direct definitions like `List A = (Maybe (Pair A B) -> B) -> B`
-- have consl and consr but only one fold!
-- it feels a lot like a droplist (List A -> List A) but without depending
-- on a previous definition of List A
consr: (A: Type) -> List A -> A -> List A
consr A xs x M mb mf = xs M (mf x mb) mf

consr': (A: Type) -> A -> List A -> List A
consr' A x xs = consr A xs x

reverse: (A: Type) -> List A -> List A
reverse A xs = xs (List A) (empty A) (consr' A)

zero: List Unit
zero = empty Unit

suc: List Unit -> List Unit
suc = consl Unit id

pair: (A: Type) -> A -> A -> List A
pair A x y M mb mf = mf x (mf y mb)

data01: List (List Unit)
data01 = pair (List Unit) zero (suc zero)

data10: List (List Unit)
data10 = pair (List Unit) (suc zero) zero

Eq: (A: Type) -> A -> A -> Type
Eq A x y = (C: A -> Type) -> C x -> C y

refl: (A: Type) -> (x: A) -> Eq A x x
refl A x C cx = cx

test_reverse: (M: Type) -> (b: M) -> (f: List Unit -> M -> M) -> \
  Eq M (data01 M b f) (reverse (List Unit) data10 M b f)
test_reverse M b f = refl M (f zero (f (suc zero) b))



Bool_to_bool: Bool -> Bool
to_bool = id Bool

Maybe_to_bool: (A: Type) -> Maybe A -> Bool
to_bool A x = case A Bool false (const Bool true A) x

Sum_to_bool: (A: Type) -> (B: Type) -> Sum A B -> Bool
to_bool A B x = case A B Bool (const Bool false A) (const Bool true B) x

Nat_to_bool: Nat -> Bool
to_bool n = case Bool false (const Bool true Nat) n

test_ol_maybe: (A: Type) -> Eq Bool (to_bool A (nothing A)) false
test A = refl Bool false

test_ol_sum: (A: Type) -> (B: Type) -> (y: B) -> \
  Eq Bool (to_bool A B (inr A B y)) true
test A B y = refl Bool true

test_ol_nat: Eq Bool (to_bool (suc (suc zero))) true
test = refl Bool true


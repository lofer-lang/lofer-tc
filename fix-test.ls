
Nat_eta: Nat -> Nat
Nat_eta = Nat_fold Nat zero suc

three: Nat
three = suc (suc (suc zero))

test: Eq Nat (Nat_eta three) three
test = refl Nat three


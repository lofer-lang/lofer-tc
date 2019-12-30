
Nat_Node: Type -> Type
Nat_Node = Maybe

Nat_Node_map_method: (A: Type) -> (B: Type) -> (A -> B) -> A -> Maybe B
Nat_Node_map_method A B f x = just B (f x)

Nat_Node_map: Mappable Nat_Node
Nat_Node_map A B f mx = mx (Nat_Node B) (nothing B) (Nat_Node_map_method A B f)

Nat: Type
Nat = Rec Nat_Node

zero: Nat
zero = Rec_close Nat_Node Nat_Node_map (nothing Nat)

suc: Nat -> Nat
suc x = Rec_close Nat_Node Nat_Node_map (just Nat x)

pred: Nat -> Maybe Nat
pred = Rec_open Maybe Nat_Node_map

Nat_case: (M: Type) -> M -> (Nat -> M) -> Nat -> M
Nat_case M x f n = pred n M x f

Nat_fold: (M: Type) -> M -> (M -> M) -> Nat -> M
Nat_fold M x f = Rec_fold Nat_Node Nat_Node_map M (Maybe_case M M x f)

postulate Nat_Fam: Type -> (Type -> Type) -> Nat -> Type
Nat_Fam = Nat_fold Type

postulate Nat_elim: (M: Nat -> Type) -> M zero -> ((n: Nat) -> M (suc n)) -> \
  (x: Nat) -> M x
Nat_elim M mz ms x = pred x (M x) mz ms

Nat_ind_step_method: (M: Nat -> Type) -> ((n: Nat) -> M n -> M (suc n)) -> \
  ((x: Nat) -> M x) -> (n: Nat) -> M (suc n)
Nat_ind_step_method M ms prev n = ms n (prev n)
Nat_ind_step: (M: Nat -> Type) -> M zero -> ((n: Nat) -> M n -> M (suc n)) -> \
  ((x: Nat) -> M x) -> (x: Nat) -> M x
Nat_ind_step M mz ms prev = Nat_elim M mz (Nat_ind_step_method M ms prev)
postulate Nat_ind: (M: Nat -> Type) -> M zero -> ((n: Nat) -> M n -> M (suc n)) -> \
  (x: Nat) -> M x
Nat_ind M mz ms = fix ((x: Nat) -> M x) id (Nat_ind_step M mz ms)


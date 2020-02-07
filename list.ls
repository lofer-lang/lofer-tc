
List_Node: Type -> Type -> Type
Node A B = Maybe (Prod A B)

List_Node_case: (A: Type) -> (B: Type) -> (M: Type) -> M -> (A -> B -> M) -> \
  List_Node A B -> M
case A B M x f = Maybe_case (Prod A B) M x (Prod_case A B M f)

List_Node_map_method: (A: Type) -> (B: Type) -> (C: Type) -> (B -> C) -> \
  A -> B -> List_Node A C
List_Node_map_method A B C f x y = just (Prod A C) (Prod_intro A C x (f y))

List_Node_map: (A: Type) -> Mappable (List_Node A)
map A B C f = List_Node_case A B (List_Node A C) \
  (nothing (Prod A C)) (List_Node_map_method A B C f)

List: Type -> Type
List A = Rec (List_Node A)

empty: (A: Type) -> List A
empty A = Rec_close (List_Node A) (List_Node_map A) (nothing (Prod A (List A)))

cons: (A: Type) -> A -> List A -> List A
cons A x xs = Rec_close (List_Node A) (List_Node_map A) \
  (just (Prod A (List A)) (Prod_intro A (List A) x xs))

uncons: (A: Type) -> List A -> Maybe (Prod A (List A))
uncons A = Rec_open (List_Node A) (List_Node_map A)

List_case: (A: Type) -> (M: Type) -> M -> (A -> List A -> M) -> List A -> M
case A M me mc xs = List_Node_case A (List A) M me mc (uncons A xs)

List_fold: (A: Type) -> (M: Type) -> M -> (A -> M -> M) -> List A -> M
fold A M me mc = Rec_fold (List_Node A) (List_Node_map A) M \
  (List_Node_case A M M me mc)

postulate List_Fam: (A: Type) -> Type -> (A -> Type -> Type) -> List A -> Type
Fam A = List_fold A Type

postulate List_elim: (A: Type) -> (M: List A -> Type) -> \
  M (empty A) -> ((x: A) -> (xs: List A) -> M (cons A x xs)) -> \
  (xs: List A) -> M xs
elim A M me mc xs = List_Node_case A (List A) (M xs) me mc xs

List_ind_step_method: (A: Type) -> (M: List A -> Type) -> \
  ((x: A) -> (xs: List A) -> M xs -> M (cons A x xs)) -> \
  ((xs: List A) -> M xs) -> \
  (x: A) -> (xs: List A) -> M (cons A x xs)
List_ind_step_method A M mc prev x xs = mc x xs (prev xs)
List_ind_step: (A: Type) -> (M: List A -> Type) -> M (empty A) -> \
  ((x: A) -> (xs: List A) -> M xs -> M (cons A x xs)) -> \
  ((xs: List A) -> M xs) -> (xs: List A) -> M xs
List_ind_step A M me mc prev = List_elim A M me (List_ind_step_method A M mc prev)
postulate List_ind: (A: Type) -> (M: List A -> Type) -> M (empty A) -> \
  ((x: A) -> (xs: List A) -> M xs -> M (cons A x xs)) -> \
  (xs: List A) ->M xs
ind A M me mc = fix ((xs: List A) -> M xs) id (List_ind_step A M me mc)


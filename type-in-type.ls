
Type: U1
Type = U0

Repr : Type
Repr = (A : Type) -> ((A -> Type) -> A) -> A

fromPolyPred : ((A : Type) -> A -> Type) -> Repr
fromPolyPred P A f = f (P A)

Const : Type -> (A : Type) -> A -> Type
Const X A y = X

fromType : Type -> Repr
fromType T = fromPolyPred (Const T)

Top : Type
Top = (C : Type) -> C -> C

ToTop : (Type -> Type) -> Type
ToTop F = F Top

toType : Repr -> Type
toType x = x Type ToTop

assert : Top
assert = previous term is a type error simply because Repr expects a Type not a Kind


Repr : Type
Repr = (A : Type) -> ((A -> Type) -> A) -> A

fromPolyPred : ((A : Type) -> A -> Type) -> Repr
fromPolyPred P A f = f (P A)

Const : Type -> (A : Type) -> A -> Type
Const X A y = X

fromType : Type -> Repr
fromType T = fromPolyPred (Const T)

postulate type_in_type: Kind -> Type
type_in_type k = k

Type': Type
Type' = type_in_type Type

Pure : (Type -> Type) -> Type
Pure F = F Unit

-- our type system does not have Type in Type! we'd HAVE to use the postulated
-- version if we were to continue with Girard's paradox
toUnit : Repr -> Type
toUnit x = x Type' Pure


Kind: U2
Kind = U1

Type: Kind
Type = U0

Void: Type
Void = (A: Type) -> A

Void_case: (A: Type) -> Void -> A
case A x = x A

Unit: Type
Unit = (A: Type) -> A -> A

id: Unit
id A x = x

const: (A: Type) -> A -> (B: Type) -> B -> A
const A x B y = x

Const: (T: Type) -> (B: Type) -> B -> Type
Const T B y = T


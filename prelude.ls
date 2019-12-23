Kind: U2
Kind = U1

Type: Kind
Type = U0

Void: Type
Void = (A: Type) -> A

void_fold: (A: Type) -> Void -> A
void_fold A x = x A

Unit: Type
Unit = (A: Type) -> A -> A

id: Unit
id A x = x

const: (A: Type) -> A -> (B: Type) -> B -> A
const A x B y = x


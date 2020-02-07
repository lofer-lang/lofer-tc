
postulate IO: Type -> Type

postulate return: (A: Type) -> A -> IO A
return A x k = x

postulate bind: (A: Type) -> (B: Type) -> (A -> IO B) -> IO A -> IO B
bind A B f x k = f (x k)

postulate abort: (A: Type) -> IO A

IO_inconsistent: (A: Type) -> Mappable (Into (Unit -> IO A))
IO_inconsistent A _ _ _ _ _ _ = abort A

IO_frob: (A: Type) -> (IO A -> IO A) -> (Unit -> IO A) -> IO A
IO_frob A f x = f (x id)

IO_fix: (A: Type) -> (IO A -> IO A) -> IO A
IO_fix A f = fix (IO A) (IO_inconsistent A) (IO_frob A f)

---------------
-- iteration

iterate_Goal: (A: Type) -> (B: Type) -> Type
iterate_Goal A B = (A -> Sum A B) -> A -> IO B

iterate_unwrap: (A: Type) -> (B: Type) -> (A -> Sum A B) -> A -> \
  iterate_Goal A B -> IO B
iterate_unwrap A B f x base = base f x

iterate_recurse: (A: Type) -> (B: Type) -> \
  IO (iterate_Goal A B) -> iterate_Goal A B
iterate_recurse A B ih f x = bind (iterate_Goal A B) B (iterate_unwrap A B f x) ih

iterate_step: (A: Type) -> (B: Type) -> \
  IO (iterate_Goal A B) -> iterate_Goal A B
iterate_step A B ih f x = f x (IO B) (iterate_recurse A B ih f) (return B)

iterate_step': (A: Type) -> (B: Type) -> \
  IO (iterate_Goal A B) -> IO (iterate_Goal A B)
iterate_step' A B ih = return (iterate_Goal A B) (iterate_step A B ih)

iterate: (A: Type) -> (B: Type) -> (A -> Sum A B) -> A -> IO B
iterate A B = iterate_recurse A B (IO_fix (iterate_Goal A B) (iterate_step' A B))

------------
-- testing

step: Bool -> Sum Bool Unit
step x = x (Sum Bool Unit) (inl Bool Unit false) (inr Bool Unit id)

alg: Bool -> IO Unit
alg = iterate Bool Unit step

postulate IO_Eq: (A: Type) -> IO A -> IO A -> Type
IO_Eq A x y = Eq A (x id) (y id)

test: IO_Eq Unit (alg true) (return Unit id)
test = refl Unit id



IntP: Type
IntP = Nat

IntP_one: IntP
one = zero

IntP_add_suc: (IntP -> IntP) -> IntP -> IntP
IntP_add_suc f x = suc (f x)

IntP_add: IntP -> IntP -> IntP
add = Nat_fold (IntP -> IntP) suc IntP_add_suc

IntP_mul: IntP -> IntP -> IntP
mul x = Nat_fold IntP x (add x)

Int: Type
Int = Signed IntP

Int_negative: IntP -> Int
negative = negative IntP

-- @Completeness Signed_zero should overload fine
Int_zero: Int
zero = Signed_zero IntP

Int_positive: IntP -> Int
positive = positive IntP

Int_negate: Int -> Int
negate = negate IntP

-- suc -n = -pred n
Int_suc_sucn: IntP -> Int
Int_suc_sucn x = pred x Int zero negative

Int_suc_sucp: IntP -> Int
Int_suc_sucp x = positive (suc x)

Int_suc: Int -> Int
suc x = x Int Int_suc_sucn (positive one) Int_suc_sucp

-- given (k -_) and y, determine (suc k) - y = suc (k - y)
IntP_diff_suc: (IntP -> Int) -> IntP -> Int
IntP_diff_suc f y = suc (f y)

IntP_diff: IntP -> IntP -> Int
diff = Nat_fold (IntP -> Int) Int_suc_sucn IntP_diff_suc

Int_add: Int -> Int -> Int
add = Signed_add IntP add diff

Int_mul: Int -> Int -> Int
mul = Signed_mul IntP mul



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

Signed: Type -> Type
Signed X = (M: Type) -> (X -> M) -> M -> (X -> M) -> M

Int: Type
Int = Signed IntP

Int_negative: IntP -> Int
negative x M n z p = n x

Int_zero: Int
zero M n z p = z

Int_positive: IntP -> Int
positive x M n z p = p x

Int_negate: Int -> Int
negate x = x Int positive zero negative

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

Int_add_nn: IntP -> IntP -> Int
Int_add_nn x y = negative (add x y)

Int_add_np: IntP -> IntP -> Int
Int_add_np x y = diff y x

Int_add_n: IntP -> Int -> Int
Int_add_n x y = y Int (Int_add_nn x) (negative x) (Int_add_np x)

Int_add_pn: IntP -> IntP -> Int
Int_add_pn x y = diff x y

Int_add_pp: IntP -> IntP -> Int
Int_add_pp x y = positive (add x y)

Int_add_p: IntP -> Int -> Int
Int_add_p x y = y Int (Int_add_pn x) (positive x) (Int_add_pp x)

Int_add: Int -> Int -> Int
add x = x (Int -> Int) Int_add_n (id Int) Int_add_p


Int_mul_same: IntP -> IntP -> Int
Int_mul_same x y = positive (mul x y)

Int_mul_diff: IntP -> IntP -> Int
Int_mul_diff x y = negative (mul x y)

Int_mul_n: IntP -> Int -> Int
Int_mul_n x y = y Int (Int_mul_same x) zero (Int_mul_diff x)

Int_mul_p: IntP -> Int -> Int
Int_mul_p x y = y Int (Int_mul_diff x) zero (Int_mul_same x)

Int_mul: Int -> Int -> Int
mul x = x (Int -> Int) Int_mul_n (const Int zero Int) Int_mul_p


Int_test_add1: Eq Int \
  (add (positive (suc one)) (positive (suc one))) \
  (positive (suc (suc (suc one))))
Int_test_add1 = refl Int (positive (suc (suc (suc one))))

Int_test_add2: Eq Int \
  (add (positive (suc one)) (negative (suc one))) \
  zero
Int_test_add2 = refl Int zero

Int_test_add3: Eq Int \
  (add (negative (suc (suc (suc one)))) (positive (suc one))) \
  (negative (suc one))
Int_test_add3 = refl Int (negative (suc one))

Int_test_add4: Eq Int (Int_add (positive one) zero) (positive one)
Int_test_add4 = refl Int (positive one)


Int_test_mul1: Eq Int \
  (mul (positive (suc one)) (positive (suc one))) \
  (positive (suc (suc (suc one))))
Int_test_mul1 = refl Int (positive (suc (suc (suc one))))

Int_test_mul2: Eq Int \
  (mul (positive (suc one)) (negative (suc one))) \
  (negative (suc (suc (suc one))))
Int_test_mul2 = refl Int (negative (suc (suc (suc one))))

Int_test_mul3: (x: IntP) -> Eq Int \
  (mul (positive x) (negative one)) \
  (negative x)
Int_test_mul3 x = refl Int (negative x)

Int_test_mul4: (x: IntP) -> Eq Int (Int_mul (positive x) zero) zero
Int_test_mul4 x = refl Int zero



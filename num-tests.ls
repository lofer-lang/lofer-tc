
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



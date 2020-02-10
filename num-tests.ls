
Int_test_add1: Eq Int \
  (add (positive (suc IntP_one)) (positive (suc IntP_one))) \
  (positive (suc (suc (suc IntP_one))))
Int_test_add1 = refl Int (positive (suc (suc (suc IntP_one))))

Int_test_add2: Eq Int \
  (add (positive (suc IntP_one)) (negative (suc IntP_one))) \
  zero
Int_test_add2 = refl Int zero

Int_test_add3: Eq Int \
  (add (negative (suc (suc (suc IntP_one)))) (positive (suc IntP_one))) \
  (negative (suc IntP_one))
Int_test_add3 = refl Int (negative (suc IntP_one))

Int_test_add4: Eq Int (Int_add (positive IntP_one) zero) (positive IntP_one)
Int_test_add4 = refl Int (positive IntP_one)


Int_test_mul1: Eq Int \
  (mul (positive (suc IntP_one)) (positive (suc IntP_one))) \
  (positive (suc (suc (suc IntP_one))))
Int_test_mul1 = refl Int (positive (suc (suc (suc IntP_one))))

Int_test_mul2: Eq Int \
  (mul (positive (suc IntP_one)) (negative (suc IntP_one))) \
  (negative (suc (suc (suc IntP_one))))
Int_test_mul2 = refl Int (negative (suc (suc (suc IntP_one))))

Int_test_mul3: (x: IntP) -> Eq Int \
  (mul (positive x) (negative IntP_one)) \
  (negative x)
Int_test_mul3 x = refl Int (negative x)

Int_test_mul4: (x: IntP) -> Eq Int (Int_mul (positive x) zero) zero
Int_test_mul4 x = refl Int zero

two: RatP
two = from_ints (suc IntP_one) IntP_one

half: RatP
half = from_ints IntP_one (suc IntP_one)

-- not a great test...
Rat_test_add: Eq Rat \
  (add \
    (add \
      (mul (positive half) (positive RatP_one)) \
      (mul (positive half) (positive two))) \
    (mul (negative half) (add (positive RatP_one) (positive two)))) \
  zero
Rat_test_add = refl Rat zero


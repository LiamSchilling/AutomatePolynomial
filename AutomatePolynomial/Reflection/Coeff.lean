import AutomatePolynomial.Util.Polynomial

namespace Polynomial

variable {R : Type*} [Semiring R]
variable (n : ℕ) (c : R) (p q : R[X])

-- compute polynomial coefficients
class Coeffs (p : R[X]) where
  n : ℕ
  C : List R
  isLength : C.length = n
  isEq : p.coeff = fun n => (C.reverse.get? n).getD 0

-- apply equality proof to coefficient at specific degree
lemma Coeffs.isEqAt {p : R[X]} [Coeffs p] :
    p.coeff n = ((Coeffs.C p).reverse.get? n).getD 0 :=
  Coeffs.isEq.symm.rec rfl

section Coeffs

variable [Coeffs p] [Coeffs q]

-- the zero polynomial has coefficients 0
@[simp]
instance instCoeffsZero : Coeffs (0 : R[X]) where
  n := 1
  C := [0]
  isLength := by simp
  isEq := sorry

@[simp]
-- the one polynomial has coefficient 1 at degree 0
instance instCoeffsOne : Coeffs (1 : R[X]) where
  n := 1
  C := [1]
  isLength := by simp
  isEq := sorry

@[simp]
-- the constant c polynomial has coefficient c at degree 0
instance instCoeffsC : Coeffs (C c : R[X]) where
  n := 1
  C := [c]
  isLength := by simp
  isEq := sorry

-- the identity polynomial has coefficient 1 at degree 1
@[simp]
instance instCoeffsX : Coeffs (X : R[X]) where
  n := 2
  C := [1, 0]
  isLength := by simp
  isEq := sorry

end Coeffs

end Polynomial

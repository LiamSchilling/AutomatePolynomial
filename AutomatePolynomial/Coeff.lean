import AutomatePolynomial.Polynomial
import AutomatePolynomial.WithBot

namespace Polynomial

variable {R : Type*} [Semiring R]
variable [NoZeroDivisors R]
variable (n : ℕ) (c : R) (p q : R[X])

-- compute polynomial coefficients
class Coeffs (p : R[X]) where
  n : ℕ
  C : List R
  isLength : C.length = n
  isEq : p.coeff = fun n => (C.reverse.get? n).getD 0

-- compute polynomial leading coefficient
class LeadingCoeff (p : R[X]) where
  c : R
  isEq : p.leadingCoeff = c

-- power of leading coefficient
@[simp]
def leadingCoeffPow [LeadingCoeff p] :=
  LeadingCoeff.c p ^ n

-- product of leading coefficients
@[simp]
def leadingCoeffMul [LeadingCoeff p] [LeadingCoeff q] :=
  LeadingCoeff.c p * LeadingCoeff.c q

-- sum of leading coefficients
@[simp]
def leadingCoeffAdd [LeadingCoeff p] [LeadingCoeff q] :=
  LeadingCoeff.c p + LeadingCoeff.c q

-- apply equality proof to coefficient at specific degree
omit [NoZeroDivisors R] in
lemma Coeffs.isEqAt {p : R[X]} [Coeffs p] : p.coeff n = ((Coeffs.C p).reverse.get? n).getD 0 :=
  Coeffs.isEq.symm.rec (rfl)

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

section LeadingCoeff

variable [LeadingCoeff p] [LeadingCoeff q]

-- the zero polynomial has leading coefficient 0
@[simp]
instance instLeadingCoeffZero : LeadingCoeff (0 : R[X]) where
  c := 0
  isEq := leadingCoeff_zero

-- the one polynomial has leading coefficient 1
@[simp]
instance instLeadingCoeffOne : LeadingCoeff (1 : R[X]) where
  c := 1
  isEq := leadingCoeff_one

-- the constant c polynomial has leading coefficient c
@[simp]
instance instLeadingCoeffC : LeadingCoeff (C c : R[X]) where
  c := c
  isEq := leadingCoeff_C c

-- the identity polynomial has leading coefficient 1
@[simp]
instance instLeadingCoeffX : LeadingCoeff (X : R[X]) where
  c := 1
  isEq := leadingCoeff_X

-- compute leading coefficient of the power of a polynomial
-- given the leading coefficient of the polynomial
-- given NoZeroDivisors
@[simp]
instance instLeadingCoeffPow : LeadingCoeff (p ^ n) where
  c := LeadingCoeff.c p ^ n
  isEq := LeadingCoeff.isEq.rec (leadingCoeff_pow p n)

-- compute leading coefficient of the product of polynomials
-- given the leading coefficient of the polynomials
-- given NoZeroDivisors
@[simp]
instance instLeadingCoeffMul : LeadingCoeff (p * q) where
  c := LeadingCoeff.c p * LeadingCoeff.c q
  isEq := LeadingCoeff.isEq.rec (LeadingCoeff.isEq.rec (leadingCoeff_mul p q))

end LeadingCoeff

end Polynomial

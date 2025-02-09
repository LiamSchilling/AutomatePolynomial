import AutomatePolynomial.Polynomial
import AutomatePolynomial.WithBot

namespace Polynomial

variable {R : Type*} [Semiring R]
variable [NoZeroDivisors R]
variable (n : ℕ) (c : R) (p q : R[X])

-- compute polynomial coefficients
class Coeffs (p : R[X]) where
  C : ℕ → R
  isEq : p.coeff = C

-- compute polynomial leading coefficient
class LeadingCoeff (p : R[X]) where
  c : R
  isEq : p.leadingCoeff = c

-- power of leading coefficient
def leadingCoeffPow [LeadingCoeff p] :=
  LeadingCoeff.c p ^ n

-- product of leading coefficients
def leadingCoeffMul [LeadingCoeff p] [LeadingCoeff q] :=
  LeadingCoeff.c p * LeadingCoeff.c q

-- sum of leading coefficients
def leadingCoeffAdd [LeadingCoeff p] [LeadingCoeff q] :=
  LeadingCoeff.c p + LeadingCoeff.c q

-- apply equality proof to coefficient at specific degree
omit [NoZeroDivisors R] in
lemma Coeffs.isEqAt {p : R[X]} [Coeffs p] : p.coeff n = Coeffs.C p n :=
  Coeffs.isEq.rec rfl

section Coeffs

variable [Coeffs p] [Coeffs q]

-- the zero polynomial has coefficients 0
instance instCoeffsZero : Coeffs (0 : R[X]) where
  C := 0
  isEq := funext coeff_zero

-- the one polynomial has coefficient 1 at degree 0
instance instCoeffsOne : Coeffs (1 : R[X]) where
  C n := if n = 0 then 1 else 0
  isEq := funext (fun _ => coeff_one)

-- the constant c polynomial has coefficient c at degree 0
instance instCoeffsC : Coeffs (C c : R[X]) where
  C n := if n = 0 then c else 0
  isEq := funext (fun _ => coeff_C)

-- the identity polynomial has coefficient 1 at degree 1
instance instCoeffsX : Coeffs (X : R[X]) where
  C n := if 1 = n then 1 else 0
  isEq := funext (fun _ => coeff_X)

-- compute coefficients of the sum of polynomials
-- given the coefficients of the polynomials
instance instCoeffsAdd : Coeffs (p + q) where
  C := Coeffs.C p + Coeffs.C q
  isEq := Coeffs.isEq.rec (Coeffs.isEq.rec (funext (coeff_add p q)))

end Coeffs

section LeadingCoeff

variable [LeadingCoeff p] [LeadingCoeff q]

-- the zero polynomial has leading coefficient 0
instance instLeadingCoeffZero : LeadingCoeff (0 : R[X]) where
  c := 0
  isEq := leadingCoeff_zero

-- the one polynomial has leading coefficient 1
instance instLeadingCoeffOne : LeadingCoeff (1 : R[X]) where
  c := 1
  isEq := leadingCoeff_one

-- the constant c polynomial has leading coefficient c
instance instLeadingCoeffC : LeadingCoeff (C c : R[X]) where
  c := c
  isEq := leadingCoeff_C c

-- the identity polynomial has leading coefficient 1
instance instLeadingCoeffX : LeadingCoeff (X : R[X]) where
  c := 1
  isEq := leadingCoeff_X

-- compute leading coefficient of the power of a polynomial
-- given the leading coefficient of the polynomial
-- given NoZeroDivisors
instance instLeadingCoeffPow : LeadingCoeff (p ^ n) where
  c := LeadingCoeff.c p ^ n
  isEq := LeadingCoeff.isEq.rec (leadingCoeff_pow p n)

-- compute leading coefficient of the product of polynomials
-- given the leading coefficient of the polynomials
-- given NoZeroDivisors
instance instLeadingCoeffMul : LeadingCoeff (p * q) where
  c := LeadingCoeff.c p * LeadingCoeff.c q
  isEq := LeadingCoeff.isEq.rec (LeadingCoeff.isEq.rec (leadingCoeff_mul p q))

end LeadingCoeff

end Polynomial

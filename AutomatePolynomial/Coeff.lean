import AutomatePolynomial.Polynomial
import AutomatePolynomial.WithBot

namespace Polynomial

variable {R : Type*} [Semiring R]
variable (n : ℕ) (c : R) (p q : R[X])

-- compute polynomial coefficients
class Coeffs (p : R[X]) where
  C : ℕ → R
  isEq : p.coeff = C

section Coeffs

variable [Coeffs p] [Coeffs q]

-- the zero polynomial has coefficients 0
instance instCoeffsZero : Coeffs (0 : R[X]) where
  C := 0
  isEq := coeff_zero n

-- the one polynomial has coefficient 1 at degree 0
instance instCoeffsOne : Coeffs (1 : R[X]) where
  C := fun n => match n with | 0 => 1 | _ => 0
  isEq := sorry

-- the constant c polynomial has coefficient c at degree 0
instance instCoeffsC : Coeffs (C c : R[X]) where
  C := fun n => match n with | 0 => c | _ => 0
  isEq := sorry

-- the identity polynomial has coefficient 1 at degree 1
instance instCoeffsX : Coeffs (X : R[X]) where
  C := fun n => match n with | 1 => 1 | _ => 0
  isEq := sorry

-- compute coefficients of the power of a polynomial
-- given the coefficients of the polynomial
instance instCoeffsPow : Coeffs (p ^ n) where
  C := sorry
  isEq := sorry

-- compute coefficients of the sum of polynomials
-- given the coefficients of the polynomials
instance instCoeffsAdd : Coeffs (p + q) where
  C := Coeffs.C p + Coeffs.C q
  isEq := Coeffs.isEq.rec (Coeffs.isEq.rec (funext (coeff_add p q)))

-- compute coefficients of the product of polynomials
-- given the coefficients of the polynomials
instance instCoeffsMul : Coeffs (p * q) where
  C := sorry
  isEq := sorry

end Coeffs

end Polynomial

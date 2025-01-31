import AutomatePolynomial.Polynomial
import AutomatePolynomial.WithBot

namespace Polynomial

variable {R : Type*} [Semiring R]
variable (n : ℕ) (c : R) (p q : R[X])

-- compute polynomial coefficients
class Coeffs (p : R[X]) where
  C : ℕ → R
  isEq : p.coeff = C

-- apply equality proof to coefficient at specific degree
lemma Coeffs.isEqAt {p : R[X]} [Coeffs p] : p.coeff n = (Coeffs.C p) n :=
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

-- compute coefficients of the power of a polynomial
-- given the coefficients of the polynomial
instance instCoeffsPow : Coeffs (p ^ n) where
  C n := sorry
  isEq := sorry

-- compute coefficients of the sum of polynomials
-- given the coefficients of the polynomials
instance instCoeffsAdd : Coeffs (p + q) where
  C := Coeffs.C p + Coeffs.C q
  isEq := Coeffs.isEq.rec (Coeffs.isEq.rec (funext (coeff_add p q)))

-- compute coefficients of the product of polynomials
-- given the coefficients of the polynomials
instance instCoeffsMul : Coeffs (p * q) where
  C n := Fin.foldl n.succ (fun c i => c + (Coeffs.C p i * Coeffs.C q i.rev)) 0
  isEq := sorry

end Coeffs

end Polynomial

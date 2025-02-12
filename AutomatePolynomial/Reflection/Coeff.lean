import AutomatePolynomial.Util.Polynomial

namespace Polynomial

variable {R : Type*} [Semiring R]
variable (n : ℕ) (c : R) (p q : R[X])

-- compute polynomial coefficients
class Coeffs (p : R[X]) where
  C : List R
  isEq : p.coeff = fun n => (C.reverse.get? n).getD 0

-- given coefficients [cn, ... c1, c0]
-- computes abstract polynomial (c0 + c1*x + ... cn*x^n)
@[simp]
noncomputable def Coeffs.expand [Coeffs p] : { q // p = q } :=
  ⟨ expandAux (Coeffs.C p) (Coeffs.C p).length rfl, sorry ⟩

-- apply equality proof to coefficient at specific degree
lemma Coeffs.isEqAt {p : R[X]} [Coeffs p] :
    p.coeff n = ((Coeffs.C p).reverse.get? n).getD 0 :=
  Coeffs.isEq.symm.rec rfl

section Coeffs

variable [Coeffs p] [Coeffs q]

-- the zero polynomial has coefficients 0
@[simp]
instance instCoeffsZero : Coeffs (0 : R[X]) where
  C := []
  isEq := sorry

-- the one polynomial has coefficient 1 at degree 0
@[simp]
instance instCoeffsOne : Coeffs (1 : R[X]) where
  C := [1]
  isEq := sorry

-- the constant c polynomial has coefficient c at degree 0
@[simp]
instance instCoeffsC : Coeffs (C c : R[X]) where
  C := [c]
  isEq := sorry

-- the identity polynomial has coefficient 1 at degree 1
@[simp]
instance instCoeffsX : Coeffs (X : R[X]) where
  C := [1, 0]
  isEq := sorry

-- compute coefficients of power
@[simp]
instance instCoeffPow : Coeffs (p ^ n) where
  C := Coeffs.powAux n (Coeffs.C p)
  isEq := sorry

-- compute coefficients of product
@[simp]
instance instCoeffMul : Coeffs (p * q) where
  C := Coeffs.mulAux (Coeffs.C p) (Coeffs.C q)
  isEq := sorry

-- compute coefficients of sum
@[simp]
instance instCoeffsAdd : Coeffs (p + q) where
  C := Coeffs.addAux (Coeffs.C p) (Coeffs.C q)
  isEq := sorry

end Coeffs

end Polynomial

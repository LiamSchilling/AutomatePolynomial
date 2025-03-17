import AutomatePolynomial.Reflection.Lemmas

open Polynomial

section Coeffs

variable [Semiring R]

-- base cases
example : (0 : R[X]).coeff 0 = 0   := by poly_reflect_coeff VIA CoeffList
  --apply Eq.trans (@Polynomial.Coeffs.isEqAt _ _ _ _ _ (Polynomial.PolyClass.instAs CoeffsList) _); simp [Polynomial.Coeffs.C, Polynomial.PolyClass.inst]
example : (0 : R[X]).coeff 1 = 0   := by reflect_coeff
example : (1 : R[X]).coeff 0 = 1   := by reflect_coeff
example : (1 : R[X]).coeff 1 = 0   := by reflect_coeff
example : (C 0 : R[X]).coeff 0 = 0 := by reflect_coeff
example : (C 0 : R[X]).coeff 1 = 0 := by reflect_coeff
example : (C 1 : R[X]).coeff 0 = 1 := by reflect_coeff
example : (C 1 : R[X]).coeff 1 = 0 := by reflect_coeff
example : (C 2 : R[X]).coeff 0 = 2 := by reflect_coeff
example : (C 2 : R[X]).coeff 1 = 0 := by reflect_coeff
example : (X : R[X]).coeff 0 = 0   := by reflect_coeff
example : (X : R[X]).coeff 1 = 1   := by reflect_coeff

-- closure cases
example : (X ^ 2 : R[X]).coeff 1 = 0     := by reflect_coeff
example : (X ^ 2 : R[X]).coeff 2 = 1     := by reflect_coeff
example : (X * X : R[X]).coeff 1 = 0     := by reflect_coeff
example : (X * X : R[X]).coeff 2 = 1     := by reflect_coeff
example : (X + 1 : R[X]).coeff 0 = 1     := by reflect_coeff
example : (X + 1 : R[X]).coeff 1 = 1     := by reflect_coeff
example : (1 + X : R[X]).coeff 0 = 1     := by reflect_coeff
example : (1 + X : R[X]).coeff 1 = 1     := by reflect_coeff
example : (X + X : R[X]).coeff 0 = 0     := by reflect_coeff
example : (X + X : R[X]).coeff 1 = 1 + 1 := by reflect_coeff

end Coeffs

section DegreeLe

variable [Semiring R]

-- base cases
example : (0 : R[X]).degree ≤ ⊥   := by reflect_degree_le
example : (1 : R[X]).degree ≤ 0   := by reflect_degree_le
example : (C 0 : R[X]).degree ≤ ⊥ := by reflect_degree_le
example : (C 1 : R[X]).degree ≤ 0 := by reflect_degree_le
example : (C 2 : R[X]).degree ≤ 0 := by reflect_degree_le
example : (X : R[X]).degree ≤ 1   := by reflect_degree_le

-- closure cases
example : (X ^ 2 : R[X]).degree ≤ 2 := by reflect_degree_le
example : (X * X : R[X]).degree ≤ 2 := by reflect_degree_le
example : (X + 1 : R[X]).degree ≤ 1 := by reflect_degree_le
example : (1 + X : R[X]).degree ≤ 1 := by reflect_degree_le
example : (X + X : R[X]).degree ≤ 1 := by reflect_degree_le

end DegreeLe

section DegreeEq

variable [Semiring R]

-- base cases
example                  : (0 : R[X]).degree = ⊥   := by reflect_degree_eq
example [Nontrivial R]   : (1 : R[X]).degree = 0   := by reflect_degree_eq
example                  : (C 0 : R[X]).degree = ⊥ := by reflect_degree_eq
example [Nontrivial R]   : (C 1 : R[X]).degree = 0 := by reflect_degree_eq
example [NeZero (2 : R)] : (C 2 : R[X]).degree = 0 := by reflect_degree_eq
example [Nontrivial R]   : (X : R[X]).degree = 1   := by reflect_degree_eq

-- closure cases
example [Nontrivial R]                      : (X ^ 2 : R[X]).degree = 2 := by reflect_degree_eq_trying
example [Nontrivial R]                      : (X * X : R[X]).degree = 2 := by reflect_degree_eq_trying
example [Nontrivial R]                      : (X + 1 : R[X]).degree = 1 := by reflect_degree_eq_trying
example [Nontrivial R]                      : (1 + X : R[X]).degree = 1 := by reflect_degree_eq_trying
example [Nontrivial R] [NeZero (1 + 1 : R)] : (X + X : R[X]).degree = 1 := by reflect_degree_eq_trying

end DegreeEq

section LeadingCoeff

variable [Semiring R]

-- base cases
example : (0 : R[X]).leadingCoeff = 0   := by reflect_leading_coeff
example : (1 : R[X]).leadingCoeff = 1   := by reflect_leading_coeff
example : (C 0 : R[X]).leadingCoeff = 0 := by reflect_leading_coeff
example : (C 1 : R[X]).leadingCoeff = 1 := by reflect_leading_coeff
example : (C 2 : R[X]).leadingCoeff = 2 := by reflect_leading_coeff
example : (X : R[X]).leadingCoeff = 1   := by reflect_leading_coeff

-- closure cases
example [Nontrivial R]                      : (X ^ 2 : R[X]).leadingCoeff = 1 ^ 2 := by reflect_leading_coeff_trying
example [Nontrivial R]                      : (X * X : R[X]).leadingCoeff = 1 * 1 := by reflect_leading_coeff_trying
example [Nontrivial R]                      : (X + 1 : R[X]).leadingCoeff = 1     := by reflect_leading_coeff_trying
example [Nontrivial R]                      : (1 + X : R[X]).leadingCoeff = 1     := by reflect_leading_coeff_trying
example [Nontrivial R] [NeZero (1 + 1 : R)] : (X + X : R[X]).leadingCoeff = 1 + 1 := by reflect_leading_coeff_trying

end LeadingCoeff

section Eval

-- base cases
example [Semiring R] : (0 : R[X]).eval 0 = 0   := by reflect_eval
example [Semiring R] : (0 : R[X]).eval 1 = 0   := by reflect_eval
example [Semiring R] : (1 : R[X]).eval 0 = 1   := by reflect_eval
example [Semiring R] : (1 : R[X]).eval 1 = 1   := by reflect_eval
example [Semiring R] : (C 0 : R[X]).eval 0 = 0 := by reflect_eval
example [Semiring R] : (C 0 : R[X]).eval 1 = 0 := by reflect_eval
example [Semiring R] : (C 1 : R[X]).eval 0 = 1 := by reflect_eval
example [Semiring R] : (C 1 : R[X]).eval 1 = 1 := by reflect_eval
example [Semiring R] : (C 2 : R[X]).eval 0 = 2 := by reflect_eval
example [Semiring R] : (C 2 : R[X]).eval 1 = 2 := by reflect_eval
example [Semiring R] : (X : R[X]).eval 0 = 0   := by reflect_eval
example [Semiring R] : (X : R[X]).eval 1 = 1   := by reflect_eval

-- closure cases
example [CommSemiring R] : (X ^ 2 : R[X]).eval 0 = 0 ^ 2 := by reflect_eval
example [CommSemiring R] : (X ^ 2 : R[X]).eval 1 = 1 ^ 2 := by reflect_eval
example [CommSemiring R] : (X * X : R[X]).eval 0 = 0 * 0 := by reflect_eval
example [CommSemiring R] : (X * X : R[X]).eval 1 = 1 * 1 := by reflect_eval
example [Semiring R]     : (X + 1 : R[X]).eval 0 = 0 + 1 := by reflect_eval
example [Semiring R]     : (X + 1 : R[X]).eval 1 = 1 + 1 := by reflect_eval
example [Semiring R]     : (1 + X : R[X]).eval 0 = 1 + 0 := by reflect_eval
example [Semiring R]     : (1 + X : R[X]).eval 1 = 1 + 1 := by reflect_eval
example [Semiring R]     : (X + X : R[X]).eval 0 = 0 + 0 := by reflect_eval
example [Semiring R]     : (X + X : R[X]).eval 1 = 1 + 1 := by reflect_eval

end Eval

section OfCoeffs

variable [Semiring R]

-- expand: closure cases
example : (X + X : R[X]) = C (1 + 1) * X := by reflect_expand
example : (X * X : R[X]) = X ^ 2         := by reflect_expand

-- degree: closure cases with explicit ring (for DecidableEq)
example : (X ^ 2 : ℤ[X]).degree = 2 := by reflect_degree_eq_of_coeffs
example : (X * X : ℤ[X]).degree = 2 := by reflect_degree_eq_of_coeffs
example : (X + 1 : ℤ[X]).degree = 1 := by reflect_degree_eq_of_coeffs
example : (1 + X : ℤ[X]).degree = 1 := by reflect_degree_eq_of_coeffs
example : (X + X : ℤ[X]).degree = 1 := by reflect_degree_eq_of_coeffs

-- leading coefficient: closure cases with explicit ring (for DecidableEq)
example : (X ^ 2 : ℤ[X]).leadingCoeff = 1 := by reflect_leading_coeff_of_coeffs
example : (X * X : ℤ[X]).leadingCoeff = 1 := by reflect_leading_coeff_of_coeffs
example : (X + 1 : ℤ[X]).leadingCoeff = 1 := by reflect_leading_coeff_of_coeffs
example : (1 + X : ℤ[X]).leadingCoeff = 1 := by reflect_leading_coeff_of_coeffs
example : (X + X : ℤ[X]).leadingCoeff = 2 := by reflect_leading_coeff_of_coeffs

end OfCoeffs

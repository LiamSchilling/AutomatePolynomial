import AutomatePolynomial.Reflection.Polynomial.Basic

open Polynomial Rfl

section DegreeLe

variable [Semiring R]

-- base cases
example : (0 : R[X]).degree ≤ ⊥   := by poly_rfl_degree_le; trivial
example : (1 : R[X]).degree ≤ 0   := by poly_rfl_degree_le; trivial
example : (C 0 : R[X]).degree ≤ ⊥ := by poly_rfl_degree_le; trivial
example : (C 1 : R[X]).degree ≤ 0 := by poly_rfl_degree_le; trivial
example : (C 2 : R[X]).degree ≤ 0 := by poly_rfl_degree_le; trivial
example : (X : R[X]).degree ≤ 1   := by poly_rfl_degree_le; trivial

-- closure cases
example : (X ^ 2 : R[X]).degree ≤ 2 := by poly_rfl_degree_le; trivial
example : (X * X : R[X]).degree ≤ 2 := by poly_rfl_degree_le; trivial
example : (X + 1 : R[X]).degree ≤ 1 := by poly_rfl_degree_le; trivial
example : (1 + X : R[X]).degree ≤ 1 := by poly_rfl_degree_le; trivial
example : (X + X : R[X]).degree ≤ 1 := by poly_rfl_degree_le; trivial

end DegreeLe

section DegreeEq

variable [Semiring R]

-- base cases
example                  : (0 : R[X]).degree = ⊥   := by poly_rfl_degree_eq
example [Nontrivial R]   : (1 : R[X]).degree = 0   := by poly_rfl_degree_eq
example                  : (C 0 : R[X]).degree = ⊥ := by poly_rfl_degree_eq
example [Nontrivial R]   : (C 1 : R[X]).degree = 0 := by poly_rfl_degree_eq
example [NeZero (2 : R)] : (C 2 : R[X]).degree = 0 := by poly_rfl_degree_eq
example [Nontrivial R]   : (X : R[X]).degree = 1   := by poly_rfl_degree_eq

-- closure cases
example [Nontrivial R]                      : ((X * X) ^ 2 : R[X]).degree = 2 + 2 := by poly_rfl_degree_eq_trying <:> poly_infer_try; trivial
example [Nontrivial R]                      : (X * X : R[X]).degree = 1 + 1       := by poly_rfl_degree_eq_trying <:> poly_infer_try
example [Nontrivial R]                      : (X + 1 : R[X]).degree = 1           := by poly_rfl_degree_eq_trying <:> poly_infer_try
example [Nontrivial R]                      : (1 + X : R[X]).degree = 1           := by poly_rfl_degree_eq_trying <:> poly_infer_try
example [Nontrivial R] [NeZero (1 + 1 : R)] : (X + X : R[X]).degree = 1           := by sorry --poly_rfl_degree_eq_trying <:> poly_infer_try

end DegreeEq

section LeadingCoeff

variable [Semiring R]

-- base cases
example : (0 : R[X]).leadingCoeff = 0   := by poly_rfl_leading_coeff
example : (1 : R[X]).leadingCoeff = 1   := by poly_rfl_leading_coeff
example : (C 0 : R[X]).leadingCoeff = 0 := by poly_rfl_leading_coeff
example : (C 1 : R[X]).leadingCoeff = 1 := by poly_rfl_leading_coeff
example : (C 2 : R[X]).leadingCoeff = 2 := by poly_rfl_leading_coeff
example : (X : R[X]).leadingCoeff = 1   := by poly_rfl_leading_coeff

-- closure cases
example [Nontrivial R]                      : ((X * X) ^ 2 : R[X]).leadingCoeff = 1 := by poly_rfl_leading_coeff_trying <:> poly_infer_try; simp
example [Nontrivial R]                      : (X * X : R[X]).leadingCoeff = 1       := by poly_rfl_leading_coeff_trying <:> poly_infer_try; simp
example [Nontrivial R]                      : (X + 1 : R[X]).leadingCoeff = 1       := by poly_rfl_leading_coeff_trying <:> poly_infer_try
example [Nontrivial R]                      : (1 + X : R[X]).leadingCoeff = 1       := by poly_rfl_leading_coeff_trying <:> poly_infer_try
example [Nontrivial R] [NeZero (1 + 1 : R)] : (X + X : R[X]).leadingCoeff = 1 + 1   := by sorry --poly_rfl_leading_coeff_trying <:> poly_infer_try

end LeadingCoeff

section Coeffs

variable [CommSemiring R]

-- base cases
example : (0 : R[X]).coeff 0 = 0   := by poly_rfl_coeff VIA CoeffsList
example : (0 : R[X]).coeff 1 = 0   := by poly_rfl_coeff VIA CoeffsList
example : (1 : R[X]).coeff 0 = 1   := by poly_rfl_coeff VIA CoeffsList; trivial
example : (1 : R[X]).coeff 1 = 0   := by poly_rfl_coeff VIA CoeffsList; trivial
example : (C 0 : R[X]).coeff 0 = 0 := by poly_rfl_coeff VIA CoeffsList
example : (C 0 : R[X]).coeff 1 = 0 := by poly_rfl_coeff VIA CoeffsList
example : (C 1 : R[X]).coeff 0 = 1 := by poly_rfl_coeff VIA CoeffsList; trivial
example : (C 1 : R[X]).coeff 1 = 0 := by poly_rfl_coeff VIA CoeffsList; trivial
example : (C 2 : R[X]).coeff 0 = 2 := by poly_rfl_coeff VIA CoeffsList; trivial
example : (C 2 : R[X]).coeff 1 = 0 := by poly_rfl_coeff VIA CoeffsList; trivial
example : (X : R[X]).coeff 0 = 0   := by poly_rfl_coeff VIA CoeffsList; trivial
example : (X : R[X]).coeff 1 = 1   := by poly_rfl_coeff VIA CoeffsList; trivial

-- closure cases
example : (X ^ 2 : R[X]).coeff 1 = 0     := by poly_rfl_coeff VIA CoeffsList; simp
example : (X ^ 2 : R[X]).coeff 2 = 1     := by poly_rfl_coeff VIA CoeffsList; simp
example : (X * X : R[X]).coeff 1 = 0     := by poly_rfl_coeff VIA CoeffsList; simp
example : (X * X : R[X]).coeff 2 = 1     := by poly_rfl_coeff VIA CoeffsList; simp
example : (X + 1 : R[X]).coeff 0 = 1     := by poly_rfl_coeff VIA CoeffsList; simp
example : (X + 1 : R[X]).coeff 1 = 1     := by poly_rfl_coeff VIA CoeffsList; simp
example : (1 + X : R[X]).coeff 0 = 1     := by poly_rfl_coeff VIA CoeffsList; simp
example : (1 + X : R[X]).coeff 1 = 1     := by poly_rfl_coeff VIA CoeffsList; simp
example : (X + X : R[X]).coeff 0 = 0     := by poly_rfl_coeff VIA CoeffsList; simp
example : (X + X : R[X]).coeff 1 = 1 + 1 := by poly_rfl_coeff VIA CoeffsList; simp

end Coeffs

section Eval

variable [CommSemiring R]

-- base cases
example : (0 : R[X]).eval 0 = 0   := by poly_rfl_eval VIA EvalArrow
example : (0 : R[X]).eval 1 = 0   := by poly_rfl_eval VIA EvalArrow
example : (1 : R[X]).eval 0 = 1   := by poly_rfl_eval VIA EvalArrow
example : (1 : R[X]).eval 1 = 1   := by poly_rfl_eval VIA EvalArrow
example : (C 0 : R[X]).eval 0 = 0 := by poly_rfl_eval VIA EvalArrow
example : (C 0 : R[X]).eval 1 = 0 := by poly_rfl_eval VIA EvalArrow
example : (C 1 : R[X]).eval 0 = 1 := by poly_rfl_eval VIA EvalArrow
example : (C 1 : R[X]).eval 1 = 1 := by poly_rfl_eval VIA EvalArrow
example : (C 2 : R[X]).eval 0 = 2 := by poly_rfl_eval VIA EvalArrow
example : (C 2 : R[X]).eval 1 = 2 := by poly_rfl_eval VIA EvalArrow
example : (X : R[X]).eval 0 = 0   := by poly_rfl_eval VIA EvalArrow
example : (X : R[X]).eval 1 = 1   := by poly_rfl_eval VIA EvalArrow

-- closure cases
example : (X ^ 2 : R[X]).eval 0 = 0 ^ 2 := by poly_rfl_eval VIA EvalArrow
example : (X ^ 2 : R[X]).eval 1 = 1 ^ 2 := by poly_rfl_eval VIA EvalArrow
example : (X * X : R[X]).eval 0 = 0 * 0 := by poly_rfl_eval VIA EvalArrow
example : (X * X : R[X]).eval 1 = 1 * 1 := by poly_rfl_eval VIA EvalArrow
example : (X + 1 : R[X]).eval 0 = 0 + 1 := by poly_rfl_eval VIA EvalArrow
example : (X + 1 : R[X]).eval 1 = 1 + 1 := by poly_rfl_eval VIA EvalArrow
example : (1 + X : R[X]).eval 0 = 1 + 0 := by poly_rfl_eval VIA EvalArrow
example : (1 + X : R[X]).eval 1 = 1 + 1 := by poly_rfl_eval VIA EvalArrow
example : (X + X : R[X]).eval 0 = 0 + 0 := by poly_rfl_eval VIA EvalArrow
example : (X + X : R[X]).eval 1 = 1 + 1 := by poly_rfl_eval VIA EvalArrow

end Eval

section OfCoeffs

variable [CommSemiring R]

-- expand: closure cases
example : (X + X : R[X]) = (1 + 1) * X := by poly_rfl_expand VIA CoeffsList; simp; unfold_expand_aux; simp
example : (X * X : R[X]) = X ^ 2       := by poly_rfl_expand VIA CoeffsList; simp; unfold_expand_aux; simp

-- degree: closure cases with explicit ring (for DecidableEq)
example : (X ^ 2 : ℤ[X]).degree = 2 := by poly_rfl_degree_eq_of_coeffs VIA CoeffsList; trivial
example : (X * X : ℤ[X]).degree = 2 := by sorry --poly_rfl_degree_eq_of_coeffs VIA CoeffsList; trivial
example : (X + 1 : ℤ[X]).degree = 1 := by sorry --poly_rfl_degree_eq_of_coeffs VIA CoeffsList; trivial
example : (1 + X : ℤ[X]).degree = 1 := by sorry --poly_rfl_degree_eq_of_coeffs VIA CoeffsList; trivial
example : (X + X : ℤ[X]).degree = 1 := by sorry --poly_rfl_degree_eq_of_coeffs VIA CoeffsList; trivial

-- leading coefficient: closure cases with explicit ring (for DecidableEq)
example : (X ^ 2 : ℤ[X]).leadingCoeff = 1 := by poly_rfl_leading_coeff_of_coeffs VIA CoeffsList; trivial
example : (X * X : ℤ[X]).leadingCoeff = 1 := by sorry --poly_rfl_leading_coeff_of_coeffs VIA CoeffsList; trivial
example : (X + 1 : ℤ[X]).leadingCoeff = 1 := by sorry --poly_rfl_leading_coeff_of_coeffs VIA CoeffsList; trivial
example : (1 + X : ℤ[X]).leadingCoeff = 1 := by sorry --poly_rfl_leading_coeff_of_coeffs VIA CoeffsList; trivial
example : (X + X : ℤ[X]).leadingCoeff = 2 := by sorry --poly_rfl_leading_coeff_of_coeffs VIA CoeffsList; trivial

end OfCoeffs

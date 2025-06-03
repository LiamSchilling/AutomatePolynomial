import AutomatePolynomial.Reflection.Polynomial.Basic

open Polynomial Rfl

section DegreeLe

variable [Semiring R]

example : (0     : R[X]).degree ≤ ⊥ := by poly_rfl_degree_le; trivial
example : (1     : R[X]).degree ≤ 0 := by poly_rfl_degree_le; trivial
example : (C 2   : R[X]).degree ≤ 0 := by poly_rfl_degree_le; trivial
example : (X     : R[X]).degree ≤ 1 := by poly_rfl_degree_le; trivial
example : (X ^ 0 : R[X]).degree ≤ 0 := by poly_rfl_degree_le; trivial
example : (X ^ 1 : R[X]).degree ≤ 1 := by poly_rfl_degree_le; trivial
example : (X ^ 2 : R[X]).degree ≤ 2 := by poly_rfl_degree_le; trivial

example : (1 ^ 2   : R[X]).degree ≤ 0 := by poly_rfl_degree_le; trivial
example : (C 2 ^ 2 : R[X]).degree ≤ 0 := by poly_rfl_degree_le; trivial
example : (X * X   : R[X]).degree ≤ 2 := by poly_rfl_degree_le; trivial
example : (1 * X   : R[X]).degree ≤ 1 := by poly_rfl_degree_le; trivial
example : (C 2 * X : R[X]).degree ≤ 1 := by poly_rfl_degree_le; trivial
example : (X * 1   : R[X]).degree ≤ 1 := by poly_rfl_degree_le; trivial
example : (X * C 2 : R[X]).degree ≤ 1 := by poly_rfl_degree_le; trivial
example : (X + X   : R[X]).degree ≤ 1 := by poly_rfl_degree_le; trivial
example : (1 + X   : R[X]).degree ≤ 1 := by poly_rfl_degree_le; trivial
example : (C 2 + X : R[X]).degree ≤ 1 := by poly_rfl_degree_le; trivial
example : (X + 1   : R[X]).degree ≤ 1 := by poly_rfl_degree_le; trivial
example : (X + C 2 : R[X]).degree ≤ 1 := by poly_rfl_degree_le; trivial

end DegreeLe

section DegreeEq

variable [Semiring R]

example                  : (0     : R[X]).degree = ⊥ := by poly_rfl_degree_eq
example [Nontrivial R]   : (1     : R[X]).degree = 0 := by poly_rfl_degree_eq
example [NeZero (2 : R)] : (C 2   : R[X]).degree = 0 := by poly_rfl_degree_eq
example [Nontrivial R]   : (X     : R[X]).degree = 1 := by poly_rfl_degree_eq
example [Nontrivial R]   : (X ^ 0 : R[X]).degree = 0 := by poly_rfl_degree_eq; trivial
example [Nontrivial R]   : (X ^ 1 : R[X]).degree = 1 := by poly_rfl_degree_eq; trivial
example [Nontrivial R]   : (X ^ 2 : R[X]).degree = 2 := by poly_rfl_degree_eq

example [Nontrivial R]       : (1 ^ 2   : R[X]).degree = 0 := by poly_rfl_degree_eq_trying <:> poly_infer_try; trivial
--example [NeZero (2 ^ 2 : R)] : (C 2 ^ 2 : R[X]).degree = 0 := by sorry
example [Nontrivial R]       : (X * X   : R[X]).degree = 2 := by poly_rfl_degree_eq_trying <:> poly_infer_try; trivial
example [Nontrivial R]       : (1 * X   : R[X]).degree = 1 := by poly_rfl_degree_eq_trying <:> poly_infer_try; trivial
--example [NeZero (2 : R)]     : (C 2 * X : R[X]).degree = 1 := by sorry
example [Nontrivial R]       : (X * 1   : R[X]).degree = 1 := by poly_rfl_degree_eq_trying <:> poly_infer_try; trivial
--example [NeZero (2 : R)]     : (X * C 2 : R[X]).degree = 1 := by sorry
--example [NeZero (2 : R)]     : (X + X   : R[X]).degree = 1 := by sorry
example [Nontrivial R]       : (1 + X   : R[X]).degree = 1 := by poly_rfl_degree_eq_trying <:> poly_infer_try
--example [NeZero (2 : R)]     : (C 2 + X : R[X]).degree = 1 := by sorry
example [Nontrivial R]       : (X + 1   : R[X]).degree = 1 := by poly_rfl_degree_eq_trying <:> poly_infer_try
--example [NeZero (2 : R)]     : (X + C 2 : R[X]).degree = 1 := by sorry

end DegreeEq

section LeadingCoeff

variable [Semiring R]

example : (0     : R[X]).leadingCoeff = 0 := by poly_rfl_leading_coeff
example : (1     : R[X]).leadingCoeff = 1 := by poly_rfl_leading_coeff
example : (C 2   : R[X]).leadingCoeff = 2 := by poly_rfl_leading_coeff
example : (X     : R[X]).leadingCoeff = 1 := by poly_rfl_leading_coeff
example : (X ^ 0 : R[X]).leadingCoeff = 1 := by poly_rfl_leading_coeff
example : (X ^ 1 : R[X]).leadingCoeff = 1 := by poly_rfl_leading_coeff
example : (X ^ 2 : R[X]).leadingCoeff = 1 := by poly_rfl_leading_coeff

example [Nontrivial R]       : (1 ^ 2   : R[X]).leadingCoeff = 1 := by poly_rfl_leading_coeff_trying <:> poly_infer_try; simp
--example [NeZero (2 ^ 2 : R)] : (C 2 ^ 2 : R[X]).leadingCoeff = 4 := by sorry
example [Nontrivial R]       : (X * X   : R[X]).leadingCoeff = 1 := by poly_rfl_leading_coeff_trying <:> poly_infer_try; simp
example [Nontrivial R]       : (1 * X   : R[X]).leadingCoeff = 1 := by poly_rfl_leading_coeff_trying <:> poly_infer_try; simp
--example [NeZero (2 : R)]     : (C 2 * X : R[X]).leadingCoeff = 2 := by sorry
example [Nontrivial R]       : (X * 1   : R[X]).leadingCoeff = 1 := by poly_rfl_leading_coeff_trying <:> poly_infer_try; simp
--example [NeZero (2 : R)]     : (X * C 2 : R[X]).leadingCoeff = 2 := by sorry
--example [NeZero (2 : R)]     : (X + X   : R[X]).leadingCoeff = 1 := by sorry
example [Nontrivial R]       : (1 + X   : R[X]).leadingCoeff = 1 := by poly_rfl_leading_coeff_trying <:> poly_infer_try
--example [NeZero (2 : R)]     : (C 2 + X : R[X]).leadingCoeff = 1 := by sorry
example [Nontrivial R]       : (X + 1   : R[X]).leadingCoeff = 1 := by poly_rfl_leading_coeff_trying <:> poly_infer_try
--example [NeZero (2 : R)]     : (X + C 2 : R[X]).leadingCoeff = 1 := by sorry

end LeadingCoeff

section Coeffs

variable [CommSemiring R]

example : (0     : R[X]).coeff 0 = 0 := by poly_rfl_coeff VIA CoeffsList
example : (1     : R[X]).coeff 0 = 1 := by poly_rfl_coeff VIA CoeffsList; trivial
example : (C 2   : R[X]).coeff 0 = 2 := by poly_rfl_coeff VIA CoeffsList; trivial
example : (X     : R[X]).coeff 0 = 0 := by poly_rfl_coeff VIA CoeffsList; trivial
example : (X ^ 0 : R[X]).coeff 0 = 1 := by poly_rfl_coeff VIA CoeffsList; trivial
example : (X ^ 1 : R[X]).coeff 0 = 0 := by poly_rfl_coeff VIA CoeffsList; trivial
example : (X ^ 2 : R[X]).coeff 0 = 0 := by poly_rfl_coeff VIA CoeffsList; trivial

example : (0     : R[X]).coeff 1 = 0 := by poly_rfl_coeff VIA CoeffsList
example : (1     : R[X]).coeff 1 = 0 := by poly_rfl_coeff VIA CoeffsList; trivial
example : (C 2   : R[X]).coeff 1 = 0 := by poly_rfl_coeff VIA CoeffsList; trivial
example : (X     : R[X]).coeff 1 = 1 := by poly_rfl_coeff VIA CoeffsList; trivial
example : (X ^ 0 : R[X]).coeff 1 = 0 := by poly_rfl_coeff VIA CoeffsList; trivial
example : (X ^ 1 : R[X]).coeff 1 = 1 := by poly_rfl_coeff VIA CoeffsList; trivial
example : (X ^ 2 : R[X]).coeff 1 = 0 := by poly_rfl_coeff VIA CoeffsList; trivial

example : (1 ^ 2   : R[X]).coeff 0 = 1 := by poly_rfl_coeff VIA CoeffsList; simp
example : (C 2 ^ 2 : R[X]).coeff 0 = 4 := by poly_rfl_coeff VIA CoeffsList; norm_num
example : (X * X   : R[X]).coeff 0 = 0 := by poly_rfl_coeff VIA CoeffsList; simp
example : (1 * X   : R[X]).coeff 0 = 0 := by poly_rfl_coeff VIA CoeffsList; simp
example : (C 2 * X : R[X]).coeff 0 = 0 := by poly_rfl_coeff VIA CoeffsList; simp
example : (X * 1   : R[X]).coeff 0 = 0 := by poly_rfl_coeff VIA CoeffsList; simp
example : (X * C 2 : R[X]).coeff 0 = 0 := by poly_rfl_coeff VIA CoeffsList; simp
example : (X + X   : R[X]).coeff 0 = 0 := by poly_rfl_coeff VIA CoeffsList; simp
example : (1 + X   : R[X]).coeff 0 = 1 := by poly_rfl_coeff VIA CoeffsList; simp
example : (C 2 + X : R[X]).coeff 0 = 2 := by poly_rfl_coeff VIA CoeffsList; simp
example : (X + 1   : R[X]).coeff 0 = 1 := by poly_rfl_coeff VIA CoeffsList; simp
example : (X + C 2 : R[X]).coeff 0 = 2 := by poly_rfl_coeff VIA CoeffsList; simp

example : (1 ^ 2   : R[X]).coeff 1 = 0 := by poly_rfl_coeff VIA CoeffsList; simp
example : (C 2 ^ 2 : R[X]).coeff 1 = 0 := by poly_rfl_coeff VIA CoeffsList; simp
example : (X * X   : R[X]).coeff 1 = 0 := by poly_rfl_coeff VIA CoeffsList; simp
example : (1 * X   : R[X]).coeff 1 = 1 := by poly_rfl_coeff VIA CoeffsList; simp
example : (C 2 * X : R[X]).coeff 1 = 2 := by poly_rfl_coeff VIA CoeffsList; simp
example : (X * 1   : R[X]).coeff 1 = 1 := by poly_rfl_coeff VIA CoeffsList; simp
example : (X * C 2 : R[X]).coeff 1 = 2 := by poly_rfl_coeff VIA CoeffsList; simp
example : (X + X   : R[X]).coeff 1 = 2 := by poly_rfl_coeff VIA CoeffsList; norm_num
example : (1 + X   : R[X]).coeff 1 = 1 := by poly_rfl_coeff VIA CoeffsList; simp
example : (C 2 + X : R[X]).coeff 1 = 1 := by poly_rfl_coeff VIA CoeffsList; simp
example : (X + 1   : R[X]).coeff 1 = 1 := by poly_rfl_coeff VIA CoeffsList; simp
example : (X + C 2 : R[X]).coeff 1 = 1 := by poly_rfl_coeff VIA CoeffsList; simp

end Coeffs

section Eval

variable [CommSemiring R]

example : (0     : R[X]).eval 0 = 0 := by poly_rfl_eval VIA EvalArrow
example : (1     : R[X]).eval 0 = 1 := by poly_rfl_eval VIA EvalArrow
example : (C 2   : R[X]).eval 0 = 2 := by poly_rfl_eval VIA EvalArrow
example : (X     : R[X]).eval 0 = 0 := by poly_rfl_eval VIA EvalArrow
example : (X ^ 0 : R[X]).eval 0 = 1 := by poly_rfl_eval VIA EvalArrow; simp
example : (X ^ 1 : R[X]).eval 0 = 0 := by poly_rfl_eval VIA EvalArrow; simp
example : (X ^ 2 : R[X]).eval 0 = 0 := by poly_rfl_eval VIA EvalArrow; simp

example : (0     : R[X]).eval 1 = 0 := by poly_rfl_eval VIA EvalArrow
example : (1     : R[X]).eval 1 = 1 := by poly_rfl_eval VIA EvalArrow
example : (C 2   : R[X]).eval 1 = 2 := by poly_rfl_eval VIA EvalArrow
example : (X     : R[X]).eval 1 = 1 := by poly_rfl_eval VIA EvalArrow
example : (X ^ 0 : R[X]).eval 1 = 1 := by poly_rfl_eval VIA EvalArrow; simp
example : (X ^ 1 : R[X]).eval 1 = 1 := by poly_rfl_eval VIA EvalArrow; simp
example : (X ^ 2 : R[X]).eval 1 = 1 := by poly_rfl_eval VIA EvalArrow; simp

example : (1 ^ 2   : R[X]).eval 0 = 1 := by poly_rfl_eval VIA EvalArrow; simp
example : (C 2 ^ 2 : R[X]).eval 0 = 4 := by poly_rfl_eval VIA EvalArrow; norm_num
example : (X * X   : R[X]).eval 0 = 0 := by poly_rfl_eval VIA EvalArrow; simp
example : (1 * X   : R[X]).eval 0 = 0 := by poly_rfl_eval VIA EvalArrow; simp
example : (C 2 * X : R[X]).eval 0 = 0 := by poly_rfl_eval VIA EvalArrow; simp
example : (X * 1   : R[X]).eval 0 = 0 := by poly_rfl_eval VIA EvalArrow; simp
example : (X * C 2 : R[X]).eval 0 = 0 := by poly_rfl_eval VIA EvalArrow; simp
example : (X + X   : R[X]).eval 0 = 0 := by poly_rfl_eval VIA EvalArrow; simp
example : (1 + X   : R[X]).eval 0 = 1 := by poly_rfl_eval VIA EvalArrow; simp
example : (C 2 + X : R[X]).eval 0 = 2 := by poly_rfl_eval VIA EvalArrow; simp
example : (X + 1   : R[X]).eval 0 = 1 := by poly_rfl_eval VIA EvalArrow; simp
example : (X + C 2 : R[X]).eval 0 = 2 := by poly_rfl_eval VIA EvalArrow; simp

example : (1 ^ 2   : R[X]).eval 1 = 1 := by poly_rfl_eval VIA EvalArrow; simp
example : (C 2 ^ 2 : R[X]).eval 1 = 4 := by poly_rfl_eval VIA EvalArrow; norm_num
example : (X * X   : R[X]).eval 1 = 1 := by poly_rfl_eval VIA EvalArrow; simp
example : (1 * X   : R[X]).eval 1 = 1 := by poly_rfl_eval VIA EvalArrow; simp
example : (C 2 * X : R[X]).eval 1 = 2 := by poly_rfl_eval VIA EvalArrow; simp
example : (X * 1   : R[X]).eval 1 = 1 := by poly_rfl_eval VIA EvalArrow; simp
example : (X * C 2 : R[X]).eval 1 = 2 := by poly_rfl_eval VIA EvalArrow; simp
example : (X + X   : R[X]).eval 1 = 2 := by poly_rfl_eval VIA EvalArrow; norm_num
example : (1 + X   : R[X]).eval 1 = 2 := by poly_rfl_eval VIA EvalArrow; norm_num
example : (C 2 + X : R[X]).eval 1 = 3 := by poly_rfl_eval VIA EvalArrow; norm_num
example : (X + 1   : R[X]).eval 1 = 2 := by poly_rfl_eval VIA EvalArrow; norm_num
example : (X + C 2 : R[X]).eval 1 = 3 := by poly_rfl_eval VIA EvalArrow; norm_num

end Eval

section OfCoeffs

variable [CommSemiring R]

example : (1 ^ 2   : R[X]) = 1       := by poly_rfl_expand VIA CoeffsList; simp; poly_unfold_expand; simp
example : (C 2 ^ 2 : R[X]) = C 4     := by poly_rfl_expand VIA CoeffsList; simp; poly_unfold_expand; norm_num
example : (X * X   : R[X]) = X ^ 2   := by poly_rfl_expand VIA CoeffsList; simp; poly_unfold_expand; simp
example : (1 * X   : R[X]) = X       := by poly_rfl_expand VIA CoeffsList; simp; poly_unfold_expand; simp
example : (C 2 * X : R[X]) = C 2 * X := by poly_rfl_expand VIA CoeffsList; simp; poly_unfold_expand; simp
example : (X * 1   : R[X]) = X       := by poly_rfl_expand VIA CoeffsList; simp; poly_unfold_expand; simp
example : (X * C 2 : R[X]) = C 2 * X := by poly_rfl_expand VIA CoeffsList; simp; poly_unfold_expand; simp
example : (X + X   : R[X]) = C 2 * X := by poly_rfl_expand VIA CoeffsList; simp; poly_unfold_expand; norm_num
example : (1 + X   : R[X]) = X + 1   := by poly_rfl_expand VIA CoeffsList; simp; poly_unfold_expand; simp
example : (C 2 + X : R[X]) = X + C 2 := by poly_rfl_expand VIA CoeffsList; simp; poly_unfold_expand; simp
example : (X + 1   : R[X]) = X + 1   := by rfl
example : (X + C 2 : R[X]) = X + C 2 := by poly_rfl_expand VIA CoeffsList; simp; poly_unfold_expand; simp

example : (1 ^ 2   : ℕ[X]).degree = 0 := by poly_rfl_degree_eq_of_coeffs VIA CoeffsList; simp; trivial
example : (C 2 ^ 2 : ℕ[X]).degree = 0 := by poly_rfl_degree_eq_of_coeffs VIA CoeffsList; simp; trivial
example : (X * X   : ℕ[X]).degree = 2 := by poly_rfl_degree_eq_of_coeffs VIA CoeffsList; simp; trivial
example : (1 * X   : ℕ[X]).degree = 1 := by poly_rfl_degree_eq_of_coeffs VIA CoeffsList; simp; trivial
example : (C 2 * X : ℕ[X]).degree = 1 := by poly_rfl_degree_eq_of_coeffs VIA CoeffsList; simp; trivial
example : (X * 1   : ℕ[X]).degree = 1 := by poly_rfl_degree_eq_of_coeffs VIA CoeffsList; simp; trivial
example : (X * C 2 : ℕ[X]).degree = 1 := by poly_rfl_degree_eq_of_coeffs VIA CoeffsList; simp; trivial
example : (X + X   : ℕ[X]).degree = 1 := by poly_rfl_degree_eq_of_coeffs VIA CoeffsList; simp; trivial
example : (1 + X   : ℕ[X]).degree = 1 := by poly_rfl_degree_eq_of_coeffs VIA CoeffsList; simp; trivial
example : (C 2 + X : ℕ[X]).degree = 1 := by poly_rfl_degree_eq_of_coeffs VIA CoeffsList; simp; trivial
example : (X + 1   : ℕ[X]).degree = 1 := by poly_rfl_degree_eq_of_coeffs VIA CoeffsList; simp; trivial
example : (X + C 2 : ℕ[X]).degree = 1 := by poly_rfl_degree_eq_of_coeffs VIA CoeffsList; simp; trivial

example : (1 ^ 2   : ℕ[X]).leadingCoeff = 1 := by poly_rfl_leading_coeff_of_coeffs VIA CoeffsList; simp
example : (C 2 ^ 2 : ℕ[X]).leadingCoeff = 4 := by poly_rfl_leading_coeff_of_coeffs VIA CoeffsList; simp
example : (X * X   : ℕ[X]).leadingCoeff = 1 := by poly_rfl_leading_coeff_of_coeffs VIA CoeffsList; simp
example : (1 * X   : ℕ[X]).leadingCoeff = 1 := by poly_rfl_leading_coeff_of_coeffs VIA CoeffsList; simp
example : (C 2 * X : ℕ[X]).leadingCoeff = 2 := by poly_rfl_leading_coeff_of_coeffs VIA CoeffsList; simp
example : (X * 1   : ℕ[X]).leadingCoeff = 1 := by poly_rfl_leading_coeff_of_coeffs VIA CoeffsList; simp
example : (X * C 2 : ℕ[X]).leadingCoeff = 2 := by poly_rfl_leading_coeff_of_coeffs VIA CoeffsList; simp
example : (X + X   : ℕ[X]).leadingCoeff = 2 := by poly_rfl_leading_coeff_of_coeffs VIA CoeffsList; simp
example : (1 + X   : ℕ[X]).leadingCoeff = 1 := by poly_rfl_leading_coeff_of_coeffs VIA CoeffsList; simp
example : (C 2 + X : ℕ[X]).leadingCoeff = 1 := by poly_rfl_leading_coeff_of_coeffs VIA CoeffsList; simp
example : (X + 1   : ℕ[X]).leadingCoeff = 1 := by poly_rfl_leading_coeff_of_coeffs VIA CoeffsList; simp
example : (X + C 2 : ℕ[X]).leadingCoeff = 1 := by poly_rfl_leading_coeff_of_coeffs VIA CoeffsList; simp

end OfCoeffs

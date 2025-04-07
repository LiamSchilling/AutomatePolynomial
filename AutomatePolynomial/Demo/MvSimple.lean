import AutomatePolynomial.Reflection.MvPolynomial.Basic

open MvPolynomial

section MvVarsLe

variable [LinearOrder σ] [CommSemiring R]

-- base cases
example : (C 0 : MvPolynomial σ R).vars ⊆ { } := by mv_poly_reflect_vars_le VIA MvVarsLeList; trivial
example : (C 1 : MvPolynomial σ R).vars ⊆ { } := by mv_poly_reflect_vars_le VIA MvVarsLeList; trivial
example : (X i : MvPolynomial σ R).vars ⊆ { i } := by mv_poly_reflect_vars_le VIA MvVarsLeList; trivial

-- closure cases
example : (X 1 + X 0 + X 1 + X 5 : MvPolynomial ℕ R).vars ⊆ { 0, 1, 5 } := by mv_poly_reflect_vars_le VIA MvVarsLeList; simp; trivial

end MvVarsLe

section MvWeightedTotalDegreeLe

variable [CommSemiring R]

-- base cases
example : (0 : MvPolynomial σ R).weightedTotalDegree 1 ≤ 0   := by mv_poly_reflect_weighted_total_degree_le; trivial
example : (1 : MvPolynomial σ R).weightedTotalDegree 1 ≤ 0   := by mv_poly_reflect_weighted_total_degree_le; trivial
example : (C 0 : MvPolynomial σ R).weightedTotalDegree 1 ≤ 0 := by mv_poly_reflect_weighted_total_degree_le; trivial
example : (C 1 : MvPolynomial σ R).weightedTotalDegree 1 ≤ 0 := by mv_poly_reflect_weighted_total_degree_le; trivial

end MvWeightedTotalDegreeLe

section MvCoeffs

variable [CommSemiring R]

-- base cases
example : (0 : MvPolynomial ℕ R).coeff 0 = 0   := by mv_poly_reflect_coeff VIA MvCoeffsHyperlist
example : (1 : MvPolynomial ℕ R).coeff 0 = 1   := by mv_poly_reflect_coeff VIA MvCoeffsHyperlist
example : (C 0 : MvPolynomial ℕ R).coeff 0 = 0 := by mv_poly_reflect_coeff VIA MvCoeffsHyperlist
example : (C 1 : MvPolynomial ℕ R).coeff 0 = 1 := by mv_poly_reflect_coeff VIA MvCoeffsHyperlist
example : (X 0 : MvPolynomial ℕ R).coeff (Finsupp.single 0 1) = 1 := by mv_poly_reflect_coeff VIA MvCoeffsHyperlist; simp [Fin.foldrM, Fin.foldrM.loop]

-- closure cases

end MvCoeffs

section MvEval

variable [CommSemiring R]

-- base cases

-- closure cases
example : ((X i + X j) ^ 2 : MvPolynomial σ R).eval 0 = 0 := by mv_poly_reflect_eval VIA MvEvalArrow; simp

end MvEval

section OfMvCoeffs

variable [CommSemiring R]

-- expand: closure cases
example : (X 1 + X 0 : MvPolynomial ℕ R) = X 0 + X 1 := by mv_poly_reflect_expand VIA MvCoeffsHyperlist; simp; unfold_mv_expand_aux; simp

end OfMvCoeffs

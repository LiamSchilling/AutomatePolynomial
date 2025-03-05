import AutomatePolynomial.Reflection.MvLemmas

open MvPolynomial

section MvCoeffs

variable [CommSemiring R]

-- base cases
example : (0 : MvPolynomial ℕ R).coeff 0 = 0   := by reflect_mv_coeff; infer_instance
example : (1 : MvPolynomial ℕ R).coeff 0 = 1   := by reflect_mv_coeff; infer_instance
example : (C 0 : MvPolynomial ℕ R).coeff 0 = 0 := by reflect_mv_coeff; infer_instance
example : (C 1 : MvPolynomial ℕ R).coeff 0 = 1 := by reflect_mv_coeff; infer_instance
example : (X 0 : MvPolynomial ℕ R).coeff (Finsupp.single 0 1) = 1 := by reflect_mv_coeff; infer_instance
-- closure cases

-- Why does this work without LinearCoeff??
example : (X 1 + 1 : MvPolynomial ℕ R).coeff 0 = 1 := by reflect_mv_coeff

end MvCoeffs

section MvDegreeLe

variable [CommSemiring R]

-- base cases
example : (0 : MvPolynomial σ R).degreeOf i ≤ 0   := by reflect_mv_degree_le
example : (1 : MvPolynomial σ R).degreeOf i ≤ 0   := by reflect_mv_degree_le
example : (C 0 : MvPolynomial σ R).degreeOf i ≤ 0 := by reflect_mv_degree_le
example : (C 1 : MvPolynomial σ R).degreeOf i ≤ 0 := by reflect_mv_degree_le
example : (X j : MvPolynomial σ R).degreeOf i ≤ 1 := by reflect_mv_degree_le

example {j i : σ} (h : j ≠ i) : (X j : MvPolynomial σ R).degreeOf i ≤ 0 := by reflect_mv_degree_le_trying

-- base cases with explicit index set (for DecidableEq)
example : (X false : MvPolynomial Bool R).degreeOf false ≤ 1 := by reflect_mv_degree_le
example : (X false : MvPolynomial Bool R).degreeOf true  ≤ 0 := by reflect_mv_degree_le
example : (X true  : MvPolynomial Bool R).degreeOf false ≤ 0 := by reflect_mv_degree_le
example : (X true  : MvPolynomial Bool R).degreeOf true  ≤ 1 := by reflect_mv_degree_le

-- closure cases
example {j i : σ} (h : j ≠ i) : (X j ^ 3 * X i ^ 2 : MvPolynomial σ R).degreeOf i ≤ 2 := by sorry
example {j i : σ} (h : j ≠ i) : (X j ^ 3 + X i ^ 2 : MvPolynomial σ R).degreeOf i ≤ 2 := by sorry

end MvDegreeLe

section OfCoeffs

variable [CommSemiring R]

end OfCoeffs

import AutomatePolynomial.Reflection.MvLemmas

open MvPolynomial

section MvCoeffs

variable [CommSemiring R]

-- base cases
example : (0 : MvPolynomial ℕ R).coeff 0 = 0   := by rw[MvCoeffs.isEqAt _]; simp [compare, compareOfLessAndEq]; infer_instance
example : (1 : MvPolynomial ℕ R).coeff 0 = 1   := by rw[MvCoeffs.isEqAt _]; simp [compare, compareOfLessAndEq]; infer_instance
example : (C 0 : MvPolynomial ℕ R).coeff 0 = 0 := by rw[MvCoeffs.isEqAt _]; simp [compare, compareOfLessAndEq]; infer_instance
example : (C 1 : MvPolynomial ℕ R).coeff 0 = 1 := by rw[MvCoeffs.isEqAt _]; simp [compare, compareOfLessAndEq]; infer_instance
example : (X 0 : MvPolynomial ℕ R).coeff (Finsupp.single 0 1) = 1 := by rw[MvPolynomial.MvCoeffs.isEqAt _]; simp [compare, compareOfLessAndEq]; infer_instance
-- closure cases

theorem getD_heq (h : HEq a (some c)) : HEq (Option.getD a b) c := by sorry
theorem getDnone_heq (h : HEq a (none : Option α)) : HEq (Option.getD a b) b := sorry
theorem get?nil_heq {L : Hyperlist α n} (h : n = 0) (h : HEq L p) : HEq (Hyperlist.get? L []) (some p) := sorry

example : (0 + 0 : MvPolynomial ℕ R).coeff 0 = 0 := by

  ---let T : MvCoeffs (X 0 + X 0 : MvPolynomial ℕ R) := by infer_instance
  rw[MvPolynomial.MvCoeffs.isEqAt _]
  simp [compare, compareOfLessAndEq]
  apply eq_of_heq; apply getD_heq; apply get?nil_heq; simp; simp
  --set x := T.C with h
  --revert h; unfold MvCoeffs.C; unfold T; intro h; simp [compare, compareOfLessAndEq, cast_eq_iff_heq] at h; sorry
  sorry

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

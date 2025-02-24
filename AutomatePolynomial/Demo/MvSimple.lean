import AutomatePolynomial.Reflection.MvLemmas

open MvPolynomial

section MvCoeffs

variable [CommSemiring R]

-- base cases
example : (0 : MvPolynomial ℕ R).coeff 0 = 0   := by rw[MvCoeffs.isEqAt _]; simp; infer_instance
example : (1 : MvPolynomial ℕ R).coeff 0 = 1   := by rw[MvCoeffs.isEqAt _]; simp; infer_instance
example : (C 0 : MvPolynomial ℕ R).coeff 0 = 0 := by rw[MvCoeffs.isEqAt _]; simp; infer_instance
example : (C 1 : MvPolynomial ℕ R).coeff 0 = 1 := by rw[MvCoeffs.isEqAt _]; simp; infer_instance
example : (X 0 : MvPolynomial ℕ R).coeff (Finsupp.single 0 1) = 1 := by rw[MvCoeffs.isEqAt _]; simp; infer_instance

-- closure cases
example : (0 + 0 : MvPolynomial ℕ R).coeff 0 = 0 := by rw[MvCoeffs.isEqAt _]; sorry;

end MvCoeffs

section MvDegreeLe

variable [CommSemiring R]

-- base cases
example : (0 : MvPolynomial σ R).degreeOf i ≤ 0   := MvDegreeLe.isLe
example : (1 : MvPolynomial σ R).degreeOf i ≤ 0   := MvDegreeLe.isLe
example : (C 0 : MvPolynomial σ R).degreeOf i ≤ 0 := MvDegreeLe.isLe
example : (C 1 : MvPolynomial σ R).degreeOf i ≤ 0 := MvDegreeLe.isLe
example : (X j : MvPolynomial σ R).degreeOf i ≤ 1 := MvDegreeLe.isLe

variable {j i : σ} in
example (h : j ≠ i) : (X j : MvPolynomial σ R).degreeOf i ≤ 0 :=
  let _ : MvDegreeLe (X j : MvPolynomial σ R) i := by infer_instance_trying
  MvDegreeLe.isLe

-- base cases with explicit index set (for DecidableEq)
example : (X false : MvPolynomial Bool R).degreeOf false ≤ 1 := MvDegreeLe.isLe
example : (X false : MvPolynomial Bool R).degreeOf true  ≤ 0 := MvDegreeLe.isLe
example : (X true  : MvPolynomial Bool R).degreeOf false ≤ 0 := MvDegreeLe.isLe
example : (X true  : MvPolynomial Bool R).degreeOf true  ≤ 1 := MvDegreeLe.isLe

-- closure cases

variable {j i : σ} in
example (h : j ≠ i) : (X j ^ 3 * X i ^ 2 : MvPolynomial σ R).degreeOf i ≤ 2 :=
  let _ : MvDegreeLe (X j ^ 3 * X i ^ 2 : MvPolynomial σ R) i := by infer_instance_trying
  sorry

variable {j i : σ} in
example (h : j ≠ i) : (X j ^ 3 + X i ^ 2 : MvPolynomial σ R).degreeOf i ≤ 2 :=
  let _ : MvDegreeLe (X j ^ 2 + X i ^ 2 : MvPolynomial σ R) i := by infer_instance_trying
  sorry

end MvDegreeLe

section OfCoeffs

variable [CommSemiring R]

end OfCoeffs

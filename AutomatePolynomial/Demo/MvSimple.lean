import AutomatePolynomial.Reflection.MvLemmas

open MvPolynomial

section DegreeLe

variable [CommSemiring R]

-- base cases
example : (0 : MvPolynomial σ R).degreeOf i ≤ 0   := MvDegreeLe.isLe
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

end DegreeLe

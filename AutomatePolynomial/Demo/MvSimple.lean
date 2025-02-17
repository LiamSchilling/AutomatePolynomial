import AutomatePolynomial.Reflection.MvLemmas
import AutomatePolynomial.Util.Tactics

open MvPolynomial

section DegreeLe

variable [CommSemiring R]

-- base cases
example             : (0 : MvPolynomial σ R).degreeOf i ≤ 0      := MvDegreeLe.isLe
example             : (C 0 : MvPolynomial σ R).degreeOf i ≤ 0    := MvDegreeLe.isLe
example             : (C 1 : MvPolynomial σ R).degreeOf i ≤ 0    := MvDegreeLe.isLe
example             : (X i : MvPolynomial Bool R).degreeOf i ≤ 1 := MvDegreeLe.isLe
example (h : j ≠ i) : (X j : MvPolynomial Bool R).degreeOf i ≤ 0 := sorry

-- closure cases
/-
example : (X ^ 2 : R[X]).degree ≤ 2 := DegreeLe.isLe
example : (X * X : R[X]).degree ≤ 2 := DegreeLe.isLe
example : (X + 1 : R[X]).degree ≤ 1 := DegreeLe.isLe
example : (1 + X : R[X]).degree ≤ 1 := DegreeLe.isLe
example : (X + X : R[X]).degree ≤ 1 := DegreeLe.isLe
-/

end DegreeLe

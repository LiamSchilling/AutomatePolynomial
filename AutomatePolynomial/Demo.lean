import AutomatePolynomial.Lemmas
import AutomatePolynomial.Tactics

open Polynomial

variable {R : Type*} [Semiring R]

section Coeffs

-- base cases
example : (0 : R[X]).coeff 0 = 0   := Coeffs.isEqAt 0
example : (0 : R[X]).coeff 1 = 0   := Coeffs.isEqAt 1
example : (1 : R[X]).coeff 0 = 1   := Coeffs.isEqAt 0
example : (1 : R[X]).coeff 1 = 0   := Coeffs.isEqAt 1
example : (C 0 : R[X]).coeff 0 = 0 := Coeffs.isEqAt 0
example : (C 0 : R[X]).coeff 1 = 0 := Coeffs.isEqAt 1
example : (C 1 : R[X]).coeff 0 = 1 := Coeffs.isEqAt 0
example : (C 1 : R[X]).coeff 1 = 0 := Coeffs.isEqAt 1
example : (C 2 : R[X]).coeff 0 = 2 := Coeffs.isEqAt 0
example : (C 2 : R[X]).coeff 1 = 0 := Coeffs.isEqAt 1
example : (X : R[X]).coeff 0 = 0   := Coeffs.isEqAt 0
example : (X : R[X]).coeff 1 = 1   := Coeffs.isEqAt 1

-- closure cases
example : (X + 1 : R[X]).coeff 0 = 0 + 1 := Coeffs.isEqAt 0
example : (X + 1 : R[X]).coeff 1 = 1 + 0 := Coeffs.isEqAt 1
example : (1 + X : R[X]).coeff 0 = 1 + 0 := Coeffs.isEqAt 0
example : (1 + X : R[X]).coeff 1 = 0 + 1 := Coeffs.isEqAt 1
example : (X + X : R[X]).coeff 0 = 0 + 0 := Coeffs.isEqAt 0
example : (X + X : R[X]).coeff 1 = 1 + 1 := Coeffs.isEqAt 1

end Coeffs

section LeadingCoeff

-- base cases
example : (0 : R[X]).leadingCoeff = 0   := LeadingCoeff.isEq
example : (1 : R[X]).leadingCoeff = 1   := LeadingCoeff.isEq
example : (C 0 : R[X]).leadingCoeff = 0 := LeadingCoeff.isEq
example : (C 1 : R[X]).leadingCoeff = 1 := LeadingCoeff.isEq
example : (C 2 : R[X]).leadingCoeff = 2 := LeadingCoeff.isEq
example : (X : R[X]).leadingCoeff = 1   := LeadingCoeff.isEq

--closure cases

example [NoZeroDivisors R] : (X ^ 2 : R[X]).leadingCoeff = 1 ^ 2 := LeadingCoeff.isEq
example [NoZeroDivisors R] : (X * X : R[X]).leadingCoeff = 1 * 1 := LeadingCoeff.isEq

-- TODO

end LeadingCoeff

section DegreeEq

-- base cases
example                  : (0 : R[X]).degree = ⊥   := DegreeEq.isEq
example [Nontrivial R]   : (1 : R[X]).degree = 0   := DegreeEq.isEq
example                  : (C 0 : R[X]).degree = ⊥ := DegreeEq.isEq
example [Nontrivial R]   : (C 1 : R[X]).degree = 0 := DegreeEq.isEq
example [NeZero (2 : R)] : (C 2 : R[X]).degree = 0 := DegreeEq.isEq
example [Nontrivial R]   : (X : R[X]).degree = 1   := DegreeEq.isEq

-- closure cases

-- TODO

end DegreeEq

section DegreeLe

-- base cases
example : (0 : R[X]).degree ≤ ⊥   := DegreeLe.isLe
example : (1 : R[X]).degree ≤ 0   := DegreeLe.isLe
example : (C 0 : R[X]).degree ≤ ⊥ := DegreeLe.isLe
example : (C 1 : R[X]).degree ≤ 0 := DegreeLe.isLe
example : (C 2 : R[X]).degree ≤ 0 := DegreeLe.isLe
example : (X : R[X]).degree ≤ 1   := DegreeLe.isLe

-- closure cases
example : (X ^ 2 : R[X]).degree ≤ 2 := DegreeLe.isLe
example : (X * X : R[X]).degree ≤ 2 := DegreeLe.isLe
example : (X + 1 : R[X]).degree ≤ 1 := DegreeLe.isLe
example : (1 + X : R[X]).degree ≤ 1 := DegreeLe.isLe
example : (X + X : R[X]).degree ≤ 1 := DegreeLe.isLe

end DegreeLe

section Eval

-- base cases
example : (0 : R[X]).eval 0 = 0   := Eval.isEqAt 0
example : (0 : R[X]).eval 1 = 0   := Eval.isEqAt 1
example : (1 : R[X]).eval 0 = 1   := Eval.isEqAt 0
example : (1 : R[X]).eval 1 = 1   := Eval.isEqAt 1
example : (C 0 : R[X]).eval 0 = 0 := Eval.isEqAt 0
example : (C 0 : R[X]).eval 1 = 0 := Eval.isEqAt 1
example : (C 1 : R[X]).eval 0 = 1 := Eval.isEqAt 0
example : (C 1 : R[X]).eval 1 = 1 := Eval.isEqAt 1
example : (C 2 : R[X]).eval 0 = 2 := Eval.isEqAt 0
example : (C 2 : R[X]).eval 1 = 2 := Eval.isEqAt 1
example : (X : R[X]).eval 0 = 0   := Eval.isEqAt 0
example : (X : R[X]).eval 1 = 1   := Eval.isEqAt 1

-- closure cases
example : (X + 1 : R[X]).coeff 0 = 0 + 1 := sorry --Eval.isEqAt 0
example : (X + 1 : R[X]).coeff 1 = 1 + 1 := sorry --Eval.isEqAt 1
example : (1 + X : R[X]).coeff 0 = 1 + 0 := sorry --Eval.isEqAt 0
example : (1 + X : R[X]).coeff 1 = 1 + 1 := sorry --Eval.isEqAt 1
example : (X + X : R[X]).coeff 0 = 0 + 0 := sorry --Eval.isEqAt 0
example : (X + X : R[X]).coeff 1 = 1 + 1 := sorry --Eval.isEqAt 1

end Eval

section OfCoeffs

-- searches

example : (X + C 8 : Int[X]).degree = 1 :=
  let _ : Coeffs (X + C 8 : Int[X]) := inferInstance
  let _ : DegreeEq (X + C 8 : Int[X]) := degreeEq_of_coeffs (X + C 8 : Int[X])
  sorry

example : (X + C 8 : Int[X]).leadingCoeff = 1 :=
  let _ : Coeffs (X + C 8 : Int[X]) := inferInstance
  let _ : DegreeEq (X + C 8 : Int[X]) := degreeEq_of_coeffs (X + C 8 : Int[X])
  let _ : LeadingCoeff (X + C 8 : Int[X]) := leadingCoeff_of_coeffs (X + C 8 : Int[X])
  sorry

end OfCoeffs

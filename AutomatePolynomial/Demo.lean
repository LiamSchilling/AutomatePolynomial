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

end Coeffs

section LeadingCoeff

-- base cases
example : (0 : R[X]).leadingCoeff = 0   := LeadingCoeff.isEq
example : (1 : R[X]).leadingCoeff = 1   := LeadingCoeff.isEq
example : (C 0 : R[X]).leadingCoeff = 0 := LeadingCoeff.isEq
example : (C 1 : R[X]).leadingCoeff = 1 := LeadingCoeff.isEq
example : (C 2 : R[X]).leadingCoeff = 2 := LeadingCoeff.isEq
example : (X : R[X]).leadingCoeff = 1   := LeadingCoeff.isEq

-- closure cases
example [NoZeroDivisors R] : (X ^ 2 : R[X]).leadingCoeff = 1 ^ 2 := LeadingCoeff.isEq
example [NoZeroDivisors R] : (X * X : R[X]).leadingCoeff = 1 * 1 := LeadingCoeff.isEq

-- user assisted closure cases

example [Nontrivial R] : (X + 1 : R[X]).leadingCoeff = 1 :=
  let _ : LeadingCoeff (X + 1 : R[X]) := by infer_instance_trying <:> ( simp )
  LeadingCoeff.isEq

example [Nontrivial R] : (1 + X : R[X]).leadingCoeff = 1 :=
  let _ : LeadingCoeff (1 + X : R[X]) := by infer_instance_trying <:> ( simp )
  LeadingCoeff.isEq

example [Nontrivial R] [NeZero (1 + 1 : R)] : (X + X : R[X]).leadingCoeff = 1 + 1 :=
  let _ : LeadingCoeff (X + X : R[X]) := by infer_instance_trying <:> ( simp )
  LeadingCoeff.isEq

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
example [Nontrivial R] [NoZeroDivisors R]     : (X ^ 2 : R[X]).degree = 2 := DegreeEq.isEq
example [Nontrivial R] [NoZeroDivisors R]     : (X * X : R[X]).degree = 2 := DegreeEq.isEq
example [Nontrivial R] [NoAdditiveInverses R] : (X + 1 : R[X]).degree = 1 := DegreeEq.isEq
example [Nontrivial R] [NoAdditiveInverses R] : (1 + X : R[X]).degree = 1 := DegreeEq.isEq
example [Nontrivial R] [NoAdditiveInverses R] : (X + X : R[X]).degree = 1 := DegreeEq.isEq

-- user assisted closure cases

example [Nontrivial R] : (X ^ 2 : R[X]).degree = 2 :=
  let _ : DegreeEq (X ^ 2 : R[X]) := by infer_instance_trying <:> ( constructor; simp )
  DegreeEq.isEq

example [Nontrivial R] : (X * X : R[X]).degree = 2 :=
  let _ : DegreeEq (X * X : R[X]) := by infer_instance_trying <:> ( constructor; simp )
  DegreeEq.isEq

example [Nontrivial R] : (X + 1 : R[X]).degree = 1 :=
  let _ : DegreeEq (X + 1 : R[X]) := by infer_instance_trying <:> ( simp )
  DegreeEq.isEq

example [Nontrivial R] : (1 + X : R[X]).degree = 1 :=
  let _ : DegreeEq (1 + X : R[X]) := by infer_instance_trying <:> ( simp )
  DegreeEq.isEq

example [Nontrivial R] [NeZero (1 + 1 : R)] : (X + X : R[X]).degree = 1 :=
  let _ : DegreeEq (X + X : R[X]) := by infer_instance_trying <:> ( simp )
  DegreeEq.isEq

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
example : (X + 1 : R[X]).eval 0 = 0 + 1 := Eval.isEqAt 0
example : (X + 1 : R[X]).eval 1 = 1 + 1 := Eval.isEqAt 1
example : (1 + X : R[X]).eval 0 = 1 + 0 := Eval.isEqAt 0
example : (1 + X : R[X]).eval 1 = 1 + 1 := Eval.isEqAt 1
example : (X + X : R[X]).eval 0 = 0 + 0 := Eval.isEqAt 0
example : (X + X : R[X]).eval 1 = 1 + 1 := Eval.isEqAt 1

end Eval

section OfCoeffs

-- searches

/-
example : (X + 1 : Int[X]).degree = 1 :=
  let _ : Coeffs (X + 1 : Int[X]) := inferInstance
  let _ : DegreeEq (X + 1 : Int[X]) := degreeEq_of_coeffs (X + 1 : Int[X])
  sorry

example : (X + 1 : Int[X]).leadingCoeff = 1 :=
  let _ : Coeffs (X + 1 : Int[X]) := inferInstance
  let _ : DegreeEq (X + 1 : Int[X]) := degreeEq_of_coeffs (X + 1 : Int[X])
  let _ : LeadingCoeff (X + 1 : Int[X]) := leadingCoeff_of_coeffs (X + 1 : Int[X])
  sorry
-/

end OfCoeffs

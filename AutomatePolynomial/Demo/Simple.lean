import AutomatePolynomial.Reflection.Lemmas
import AutomatePolynomial.Util.Tactics

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
example : (X ^ 2 : R[X]).coeff 1 = 0     := by rw[Coeffs.isEq]; simp
example : (X ^ 2 : R[X]).coeff 2 = 1     := by rw[Coeffs.isEq]; simp
example : (X * X : R[X]).coeff 1 = 0     := by rw[Coeffs.isEq]; simp
example : (X * X : R[X]).coeff 2 = 1     := by rw[Coeffs.isEq]; simp
example : (X + 1 : R[X]).coeff 0 = 1     := by rw[Coeffs.isEq]; simp
example : (X + 1 : R[X]).coeff 1 = 1     := by rw[Coeffs.isEq]; simp
example : (1 + X : R[X]).coeff 0 = 1     := by rw[Coeffs.isEq]; simp
example : (1 + X : R[X]).coeff 1 = 1     := by rw[Coeffs.isEq]; simp
example : (X + X : R[X]).coeff 0 = 0     := by rw[Coeffs.isEq]; simp
example : (X + X : R[X]).coeff 1 = 1 + 1 := by rw[Coeffs.isEq]; simp

end Coeffs

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

section DegreeEq

-- base cases
example                  : (0 : R[X]).degree = ⊥   := DegreeEq.isEq
example [Nontrivial R]   : (1 : R[X]).degree = 0   := DegreeEq.isEq
example                  : (C 0 : R[X]).degree = ⊥ := DegreeEq.isEq
example [Nontrivial R]   : (C 1 : R[X]).degree = 0 := DegreeEq.isEq
example [NeZero (2 : R)] : (C 2 : R[X]).degree = 0 := DegreeEq.isEq
example [Nontrivial R]   : (X : R[X]).degree = 1   := DegreeEq.isEq

-- closure cases

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
  let _ : DegreeEq (X + X : R[X]) := by infer_instance_supposing [ ]
  DegreeEq.isEq

end DegreeEq

section LeadingCoeff

-- base cases
example : (0 : R[X]).leadingCoeff = 0   := LeadingCoeff.isEq
example : (1 : R[X]).leadingCoeff = 1   := LeadingCoeff.isEq
example : (C 0 : R[X]).leadingCoeff = 0 := LeadingCoeff.isEq
example : (C 1 : R[X]).leadingCoeff = 1 := LeadingCoeff.isEq
example : (C 2 : R[X]).leadingCoeff = 2 := LeadingCoeff.isEq
example : (X : R[X]).leadingCoeff = 1   := LeadingCoeff.isEq

-- closure cases

example [Nontrivial R] : (X ^ 2 : R[X]).leadingCoeff = 1 ^ 2 :=
  let _ : LeadingCoeff (X ^ 2 : R[X]) := by infer_instance_trying <:> ( constructor; simp )
  LeadingCoeff.isEq

example [Nontrivial R] : (X * X : R[X]).leadingCoeff = 1 * 1 :=
  let _ : LeadingCoeff (X * X : R[X]) := by infer_instance_trying <:> ( constructor; simp )
  LeadingCoeff.isEq

example [Nontrivial R] : (X + 1 : R[X]).leadingCoeff = 1 :=
  let _ : LeadingCoeff (X + 1 : R[X]) := by infer_instance_trying <:> ( simp )
  LeadingCoeff.isEq

example [Nontrivial R] : (1 + X : R[X]).leadingCoeff = 1 :=
  let _ : LeadingCoeff (1 + X : R[X]) := by infer_instance_trying <:> ( simp )
  LeadingCoeff.isEq

example [Nontrivial R] [NeZero (1 + 1 : R)] : (X + X : R[X]).leadingCoeff = 1 + 1 :=
  let _ : LeadingCoeff (X + X : R[X]) := by infer_instance_supposing [ ]
  LeadingCoeff.isEq

end LeadingCoeff

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
example : (X ^ 2 : R[X]).eval 0 = 0 ^ 2 := Eval.isEqAt 0
example : (X ^ 2 : R[X]).eval 1 = 1 ^ 2 := Eval.isEqAt 1
example : (X * X : R[X]).eval 0 = 0 * 0 := Eval.isEqAt 0
example : (X * X : R[X]).eval 1 = 1 * 1 := Eval.isEqAt 1
example : (X + 1 : R[X]).eval 0 = 0 + 1 := Eval.isEqAt 0
example : (X + 1 : R[X]).eval 1 = 1 + 1 := Eval.isEqAt 1
example : (1 + X : R[X]).eval 0 = 1 + 0 := Eval.isEqAt 0
example : (1 + X : R[X]).eval 1 = 1 + 1 := Eval.isEqAt 1
example : (X + X : R[X]).eval 0 = 0 + 0 := Eval.isEqAt 0
example : (X + X : R[X]).eval 1 = 1 + 1 := Eval.isEqAt 1

end Eval

section OfCoeffs

-- expand: closure cases

example : (X + X : R[X]) = (1 + 1) * X := by
  rw[(Coeffs.expand (X + X : R[X])).property]
  simp; unfold_expand_aux; simp

example : (X * X : R[X]) = X ^ 2 := by
  rw[(Coeffs.expand (X * X : R[X])).property]
  simp; unfold_expand_aux; simp

-- degree: closure cases with explicit ring (for DecidableEq)

example : (X ^ 2 : ℤ[X]).degree = 2 :=
  let _ : DegreeEq (X ^ 2 : ℤ[X]) := degreeEq_of_coeffs _
  DegreeEq.isEq

example : (X * X : ℤ[X]).degree = 2 :=
  let _ : DegreeEq (X * X : ℤ[X]) := degreeEq_of_coeffs _
  DegreeEq.isEq

example : (X + 1 : ℤ[X]).degree = 1 :=
  let _ : DegreeEq (X + 1 : ℤ[X]) := degreeEq_of_coeffs _
  DegreeEq.isEq

example : (1 + X : ℤ[X]).degree = 1 :=
  let _ : DegreeEq (1 + X : ℤ[X]) := degreeEq_of_coeffs _
  DegreeEq.isEq

example : (X + X : ℤ[X]).degree = 1 :=
  let _ : DegreeEq (X + X : ℤ[X]) := degreeEq_of_coeffs _
  DegreeEq.isEq

-- leading coefficient: closure cases with explicit ring (for DecidableEq)

example : (X ^ 2 : ℤ[X]).leadingCoeff = 1 :=
  let _ : LeadingCoeff (X ^ 2 : ℤ[X]) := leadingCoeff_of_coeffs _
  LeadingCoeff.isEq

example : (X * X : ℤ[X]).leadingCoeff = 1 :=
  let _ : LeadingCoeff (X * X : ℤ[X]) := leadingCoeff_of_coeffs _
  LeadingCoeff.isEq

example : (X + 1 : ℤ[X]).leadingCoeff = 1 :=
  let _ : LeadingCoeff (X + 1 : ℤ[X]) := leadingCoeff_of_coeffs _
  LeadingCoeff.isEq

example : (1 + X : ℤ[X]).leadingCoeff = 1 :=
  let _ : LeadingCoeff (1 + X : ℤ[X]) := leadingCoeff_of_coeffs _
  LeadingCoeff.isEq

example : (X + X : ℤ[X]).leadingCoeff = 2 :=
  let _ : LeadingCoeff (X + X : ℤ[X]) := leadingCoeff_of_coeffs _
  LeadingCoeff.isEq

end OfCoeffs

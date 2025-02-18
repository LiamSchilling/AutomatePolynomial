import AutomatePolynomial.Reflection.Lemmas
import AutomatePolynomial.Util.Tactics

open Polynomial

section Coeffs

variable [Semiring R]

-- base cases
example : (0 : R[X]).coeff 0 = 0   := by reflect_coeff
example : (0 : R[X]).coeff 1 = 0   := by reflect_coeff
example : (1 : R[X]).coeff 0 = 1   := by reflect_coeff
example : (1 : R[X]).coeff 1 = 0   := by reflect_coeff
example : (C 0 : R[X]).coeff 0 = 0 := by reflect_coeff
example : (C 0 : R[X]).coeff 1 = 0 := by reflect_coeff
example : (C 1 : R[X]).coeff 0 = 1 := by reflect_coeff
example : (C 1 : R[X]).coeff 1 = 0 := by reflect_coeff
example : (C 2 : R[X]).coeff 0 = 2 := by reflect_coeff
example : (C 2 : R[X]).coeff 1 = 0 := by reflect_coeff
example : (X : R[X]).coeff 0 = 0   := by reflect_coeff
example : (X : R[X]).coeff 1 = 1   := by reflect_coeff

-- closure cases
example : (X ^ 2 : R[X]).coeff 1 = 0     := by reflect_coeff
example : (X ^ 2 : R[X]).coeff 2 = 1     := by reflect_coeff
example : (X * X : R[X]).coeff 1 = 0     := by reflect_coeff
example : (X * X : R[X]).coeff 2 = 1     := by reflect_coeff
example : (X + 1 : R[X]).coeff 0 = 1     := by reflect_coeff
example : (X + 1 : R[X]).coeff 1 = 1     := by reflect_coeff
example : (1 + X : R[X]).coeff 0 = 1     := by reflect_coeff
example : (1 + X : R[X]).coeff 1 = 1     := by reflect_coeff
example : (X + X : R[X]).coeff 0 = 0     := by reflect_coeff
example : (X + X : R[X]).coeff 1 = 1 + 1 := by reflect_coeff

end Coeffs

section DegreeLe

variable [Semiring R]

-- base cases
example : (0 : R[X]).degree ≤ ⊥   := by reflect_degree_le
example : (1 : R[X]).degree ≤ 0   := by reflect_degree_le
example : (C 0 : R[X]).degree ≤ ⊥ := by reflect_degree_le
example : (C 1 : R[X]).degree ≤ 0 := by reflect_degree_le
example : (C 2 : R[X]).degree ≤ 0 := by reflect_degree_le
example : (X : R[X]).degree ≤ 1   := by reflect_degree_le

-- closure cases
example : (X ^ 2 : R[X]).degree ≤ 2 := by reflect_degree_le
example : (X * X : R[X]).degree ≤ 2 := by reflect_degree_le
example : (X + 1 : R[X]).degree ≤ 1 := by reflect_degree_le
example : (1 + X : R[X]).degree ≤ 1 := by reflect_degree_le
example : (X + X : R[X]).degree ≤ 1 := by reflect_degree_le

end DegreeLe

section DegreeEq

variable [Semiring R]

-- base cases
example                  : (0 : R[X]).degree = ⊥   := by reflect_degree_eq
example [Nontrivial R]   : (1 : R[X]).degree = 0   := by reflect_degree_eq
example                  : (C 0 : R[X]).degree = ⊥ := by reflect_degree_eq
example [Nontrivial R]   : (C 1 : R[X]).degree = 0 := by reflect_degree_eq
example [NeZero (2 : R)] : (C 2 : R[X]).degree = 0 := by reflect_degree_eq
example [Nontrivial R]   : (X : R[X]).degree = 1   := by reflect_degree_eq

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
  let _ : DegreeEq (X + X : R[X]) := by infer_instance_trying
  DegreeEq.isEq

end DegreeEq

section LeadingCoeff

variable [Semiring R]

-- base cases
example : (0 : R[X]).leadingCoeff = 0   := by reflect_leading_coeff
example : (1 : R[X]).leadingCoeff = 1   := by reflect_leading_coeff
example : (C 0 : R[X]).leadingCoeff = 0 := by reflect_leading_coeff
example : (C 1 : R[X]).leadingCoeff = 1 := by reflect_leading_coeff
example : (C 2 : R[X]).leadingCoeff = 2 := by reflect_leading_coeff
example : (X : R[X]).leadingCoeff = 1   := by reflect_leading_coeff

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
  let _ : LeadingCoeff (X + X : R[X]) := by infer_instance_trying
  LeadingCoeff.isEq

end LeadingCoeff

section Eval

-- base cases
example [Semiring R] : (0 : R[X]).eval 0 = 0   := by reflect_eval
example [Semiring R] : (0 : R[X]).eval 1 = 0   := by reflect_eval
example [Semiring R] : (1 : R[X]).eval 0 = 1   := by reflect_eval
example [Semiring R] : (1 : R[X]).eval 1 = 1   := by reflect_eval
example [Semiring R] : (C 0 : R[X]).eval 0 = 0 := by reflect_eval
example [Semiring R] : (C 0 : R[X]).eval 1 = 0 := by reflect_eval
example [Semiring R] : (C 1 : R[X]).eval 0 = 1 := by reflect_eval
example [Semiring R] : (C 1 : R[X]).eval 1 = 1 := by reflect_eval
example [Semiring R] : (C 2 : R[X]).eval 0 = 2 := by reflect_eval
example [Semiring R] : (C 2 : R[X]).eval 1 = 2 := by reflect_eval
example [Semiring R] : (X : R[X]).eval 0 = 0   := by reflect_eval
example [Semiring R] : (X : R[X]).eval 1 = 1   := by reflect_eval

-- closure cases
example [CommSemiring R] : (X ^ 2 : R[X]).eval 0 = 0 ^ 2 := by reflect_eval
example [CommSemiring R] : (X ^ 2 : R[X]).eval 1 = 1 ^ 2 := by reflect_eval
example [CommSemiring R] : (X * X : R[X]).eval 0 = 0 * 0 := by reflect_eval
example [CommSemiring R] : (X * X : R[X]).eval 1 = 1 * 1 := by reflect_eval
example [Semiring R]     : (X + 1 : R[X]).eval 0 = 0 + 1 := by reflect_eval
example [Semiring R]     : (X + 1 : R[X]).eval 1 = 1 + 1 := by reflect_eval
example [Semiring R]     : (1 + X : R[X]).eval 0 = 1 + 0 := by reflect_eval
example [Semiring R]     : (1 + X : R[X]).eval 1 = 1 + 1 := by reflect_eval
example [Semiring R]     : (X + X : R[X]).eval 0 = 0 + 0 := by reflect_eval
example [Semiring R]     : (X + X : R[X]).eval 1 = 1 + 1 := by reflect_eval

end Eval

section OfCoeffs

variable [Semiring R]

-- expand: closure cases

example : (X + X : R[X]) = C (1 + 1) * X := by
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

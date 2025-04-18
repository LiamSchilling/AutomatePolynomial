import AutomatePolynomial.Reflection.Polynomial.Defs
import AutomatePolynomial.Representation.Polynomial.CoeffList

/-!
# *Implementation*: Coefficient Lists

 -/

namespace Polynomial.Rfl

open CoeffList

variable [CommSemiring R]

/-- A list representation of polynomial coefficients -/
abbrev CoeffsList :=
  Coeffs (fun _ => List R) (fun _ C n => List.getD C n 0)

/-- A reflection system for `Coeffs` using the `CoeffList` representation -/
noncomputable instance instCoeffsListReflection :
    CoeffsNormalizerReflection R (fun _ => List R) (fun _ C n => List.getD C n 0) where

  mk_zero := {
    C := []
    isEq := by
      funext; rw[C_0]; apply reps_zero }

  mk_C c := {
    C := [c]
    isEq := by
      funext n; apply reps_C }

  mk_X := {
    C := [0, 1]
    isEq := by
      funext n; apply reps_X }

  mk_XPow N := {
    C := mulXPow N [1]
    isEq := by
      funext; rw[←mul_one (X ^ N)]; apply reps_mulXPow
      intro n; rw[coeff_one]; cases n; simp; simp }

  mk_pow n P := {
    C := power n P.C
    isEq := by
      funext; apply reps_power
      . unfold reps; rw[P.isEq]; simp }

  mk_mul P Q := {
    C := mul P.C Q.C
    isEq := by
      funext; apply reps_mul
      . unfold reps; rw[P.isEq]; simp
      . unfold reps; rw[Q.isEq]; simp }

  mk_add P Q := {
    C := add P.C Q.C
    isEq := by
      funext; apply reps_add
      . unfold reps; rw[P.isEq]; simp
      . unfold reps; rw[Q.isEq]; simp }

  mk_normalizer p := {
    Normal := { T | normal T.C }
    normalize T := ⟨
      ⟨normalize T.C, by
        funext; apply reps_normalize; unfold reps; rw[T.isEq]; simp ⟩, by
        apply normal_normalize ⟩
    normalize_idem := by intro T h; simp only [←normalize_idem h] }

  degreeEq_of_normal := by
    intro _ _ ⟨P, h⟩; exact
    ⟨degree_if_normal P.C, by apply degree_eq_of_normal h; unfold reps; rw[P.isEq]; simp⟩

  leadingCoeff_of_normal := by
    unfold Normalizer.Normal; intro _ _ ⟨P, h⟩; simp at h; exact
    ⟨leadingCoeff_if_normal P.C, by apply leadingCoeff_eq_of_normal h; unfold reps; rw[P.isEq]; simp⟩

  transform P := ⟨
    expand P.C 0, by
      apply expand_eq
      . intros; contradiction
      . intro; rw[P.isEq]; simp ⟩

end Polynomial.Rfl

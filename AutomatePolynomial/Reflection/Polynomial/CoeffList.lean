import AutomatePolynomial.Reflection.Polynomial.Defs
import AutomatePolynomial.Representation.Polynomial.CoeffList

/-!
# *Implementation*: Coefficient Lists

 -/

namespace Polynomial.Rfl

open CoeffList

variable [CommSemiring R]

/-- A list representation of polynomial evaluations -/
abbrev CoeffsList :=
  Coeffs (fun _ => List R) (fun _ C n => List.getD C n 0)

/-- A reflection system for `Coeffs` using the `CoeffList` representation -/
noncomputable instance instCoeffsListReflection :
    CoeffsNormalizerReflection R (fun _ => List R) (fun _ C n => List.getD C n 0) where

  mk_zero := {
    C := []
    isEq := by
      funext; simp }

  mk_C c := {
    C := [c]
    isEq := by
      funext n; rw[coeff_C]; cases n; simp; simp }

  mk_X := {
    C := [0, 1]
    isEq := by
      funext n; rw[coeff_X]; cases n; simp; rename_i n; cases n; simp; simp }

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
    Normal := { T | match T.C.reverse with | [] => True | c :: _ => 0 ≠ c }
    normalize T := ⟨⟨(T.C.reverse.dropWhile (Eq 0 : R → Prop)).reverse, sorry⟩, sorry⟩
    normalize_idem := by
      intro T h; simp at h
      cases hh : T.C.reverse
      . simp; simp_rw[←List.reverse_eq_nil_iff.mp hh]
      . rw[List.dropWhile_cons_of_neg, ←hh, List.reverse_reverse]; rw[hh] at h; simp; exact h }

  degreeEq_of_normal := by
    unfold Normalizer.Normal; intro _ _ ⟨P, h⟩; simp at h; exact
    ⟨match P.C with | [] => ⊥ | _ :: cs => cs.length, by
      cases hh : P.C.reverse
      . rw[List.reverse_eq_nil_iff.mp hh]; simp
        have hhh := P.isEq
        rw[List.reverse_eq_nil_iff.mp hh] at hhh; simp at hhh
        apply leadingCoeff_eq_zero.mp; unfold leadingCoeff; rw[hhh]
      . sorry ⟩

  leadingCoeff_of_normal := by
    unfold Normalizer.Normal; intro _ _ ⟨P, h⟩; simp at h; exact
    ⟨match P.C.reverse with | [] => 0 | c :: _ => c, by
      cases hh : P.C.reverse
      . simp
        apply leadingCoeff_eq_zero.mp; unfold leadingCoeff
        rw[P.isEq, List.reverse_eq_nil_iff.mp hh]; simp
      . sorry ⟩

  transform P := ⟨
    expandAux P.C 0, by
      apply expandAux_eq
      . intros; contradiction
      . intro; rw[P.isEq]; simp ⟩

end Polynomial.Rfl

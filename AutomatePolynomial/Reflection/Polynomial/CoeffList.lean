import AutomatePolynomial.Reflection.Polynomial.Defs
import AutomatePolynomial.Representation.Polynomial.CoeffList

namespace Polynomial

variable [CommSemiring R]

abbrev CoeffsList := Coeffs (fun _ => List R) (fun _ C n => List.getD C n 0)

noncomputable instance instCoeffsListReflection : CoeffsNormalReflection R (fun _ => List R) (fun _ C n => List.getD C n 0) where

  mk_zero := {
    C := []
    isEq := by funext; simp }

  mk_C c := {
    C := [c]
    isEq := by funext n; rw[coeff_C]; cases n; simp; simp }

  mk_X := {
    C := [0, 1]
    isEq := by funext n; rw[coeff_X]; cases n; simp; rename_i n; cases n; simp; simp }

  mk_XPow N := {
    C := Coeffs.mulXPowAux N [1]
    isEq := by funext; rw[←mul_one (X ^ N)]; apply Coeffs.mulXPowAux_rep; unfold is_coeff; intro n; rw[coeff_one]; cases n <;> simp }

  mk_pow _ n P := {
    C := Coeffs.powAux n P.C
    isEq := by funext; apply Coeffs.powAux_rep; unfold is_coeff; rw[P.isEq]; simp }

  mk_mul _ _ P Q := {
    C := Coeffs.mulAux P.C Q.C
    isEq := by funext; apply Coeffs.mulAux_rep; unfold is_coeff; rw[P.isEq]; simp; unfold is_coeff; rw[Q.isEq]; simp }

  mk_add _ _ P Q := {
    C := Coeffs.addAux P.C Q.C
    isEq := by funext; apply Coeffs.addAux_rep; unfold is_coeff; rw[P.isEq]; simp; unfold is_coeff; rw[Q.isEq]; simp }

  mk_norm p := {
    Normal := { T | match T.C.reverse with | [] => True | c :: _ => 0 ≠ c }
    normalize T := ⟨⟨(T.C.reverse.dropWhile (Eq 0 : R → Prop)).reverse, sorry⟩, sorry⟩
    normalize_idempotent := by
      intro T h; simp at h
      cases hh : T.C.reverse
      . simp; simp_rw[←List.reverse_eq_nil_iff.mp hh]
      . rw[List.dropWhile_cons_of_neg, ←hh, List.reverse_reverse]; rw[hh] at h; simp; exact h }

  degreeEq_of_normal := by
    unfold Normalizer.Normal; intro _ _ ⟨T, h⟩; simp at h; exact
    ⟨match T.C with | [] => ⊥ | _ :: cs => cs.length, by
      cases hh : T.C.reverse
      . rw[List.reverse_eq_nil_iff.mp hh]; simp
        have hhh := T.isEq
        rw[List.reverse_eq_nil_iff.mp hh] at hhh; simp at hhh
        apply leadingCoeff_eq_zero.mp; unfold leadingCoeff; rw[hhh]
      . sorry ⟩

  leadingCoeff_of_normal := by
    unfold Normalizer.Normal; intro _ _ ⟨T, h⟩; simp at h; exact
    ⟨match T.C.reverse with | [] => 0 | c :: _ => c, by
      cases hh : T.C.reverse
      . simp
        apply leadingCoeff_eq_zero.mp; unfold leadingCoeff; rw[T.isEq, List.reverse_eq_nil_iff.mp hh]; simp
      . sorry ⟩

  transform T := ⟨
    Coeffs.expandAux T.C 0, by
      apply Coeffs.expandAux_eq
      . intros; contradiction
      . intro; rw[T.isEq]; simp ⟩

end Polynomial

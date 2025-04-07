import AutomatePolynomial.Reflection.Polynomial.Defs

namespace Polynomial

variable [CommSemiring R]

abbrev CoeffsArrow := Coeffs (fun _ => ℕ → R) (fun _ C => C)

instance instCoeffsArrowReflection : CoeffsReflection R (fun _ => ℕ → R) (fun _ C => C) where

  mk_zero := {
    C _ := 0
    isEq := by funext; simp }

  mk_C c := {
    C n := if n = 0 then c else 0
    isEq := by funext; exact coeff_C }

  mk_X := {
    C n := if 1 = n then 1 else 0
    isEq := by funext; exact coeff_X }

  mk_XPow N := {
    C n := if n = N then 1 else 0
    isEq := by funext; exact coeff_X_pow N _ }

  mk_pow _ N P := {
    C n := sorry
    isEq := sorry }

  mk_mul _ _ P Q := {
    C n := ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, P.C x.1 * Q.C x.2
    isEq := by funext; sorry }

  mk_add _ _ P Q := {
    C n := P.C n + Q.C n
    isEq := by funext; simp[P.isEqAt, Q.isEqAt] }

end Polynomial

import AutomatePolynomial.Reflection.Polynomial.Defs

namespace Polynomial

variable [Semiring R]

abbrev CoeffsArrow := Coeffs (ℕ → R) id

instance instCoeffsArrowReflection : CoeffsReflection R (ℕ → R) id where

  mk_zero := {
    C _ := 0
    isEq := sorry }

  mk_C c := {
    C n := if n = 0 then c else 0
    isEq := sorry }

  mk_X := {
    C n := if n = 1 then 1 else 0
    isEq := sorry }

  mk_XPow N := {
    C n := if n = N then 1 else 0
    isEq := sorry }

  mk_pow _ n P := {
    C n := sorry
    isEq := sorry }

  mk_mul _ _ P Q := {
    C n := sorry
    isEq := sorry }

  mk_add _ _ P Q := {
    C n := P.C n + Q.C n
    isEq := sorry }

end Polynomial

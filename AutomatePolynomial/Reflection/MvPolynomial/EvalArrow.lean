import AutomatePolynomial.Reflection.MvPolynomial.Defs

namespace MvPolynomial

variable {σ : Type*}
variable [CommSemiring R]

abbrev MvEvalArrow := MvEval (fun _ => (σ → R) → R) (fun _ F => F)

instance instEvalArrowReflection : MvEvalReflection σ R (fun _ => (σ → R) → R) (fun _ F => F) where

  mk_zero := {
    F _ := 0
    isEq := sorry }

  mk_C c := {
    F _ := c
    isEq := sorry }

  mk_X i := {
    F x := x i
    isEq := sorry }

  mk_XPow i n := {
    F x := x i ^ n
    isEq := sorry }

  mk_pow _ n P := {
    F x := P.F x ^ n
    isEq := sorry }

  mk_mul _ _ P Q := {
    F x := P.F x * Q.F x
    isEq := sorry }

  mk_add _ _ P Q := {
    F x := P.F x + Q.F x
    isEq := sorry }

end MvPolynomial

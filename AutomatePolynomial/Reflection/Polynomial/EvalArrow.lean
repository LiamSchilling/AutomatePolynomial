import AutomatePolynomial.Reflection.Polynomial.Defs

namespace Polynomial

variable [CommSemiring R]

abbrev EvalArrow := Eval (fun _ => R → R) (fun _ F => F)

instance instEvalArrowReflection : EvalReflection R (fun _ => R → R) (fun _ F => F) where

  mk_zero := {
    F _ := 0
    isEq := by simp }

  mk_C c := {
    F _ := c
    isEq := by simp }

  mk_X := {
    F x := x
    isEq := by simp }

  mk_XPow n := {
    F x := x ^ n
    isEq := by simp }

  mk_pow _ n P := {
    F x := P.F x ^ n
    isEq := by simp [P.isEqAt] }

  mk_mul _ _ P Q := {
    F x := P.F x * Q.F x
    isEq := by simp [P.isEqAt, Q.isEqAt] }

  mk_add _ _ P Q := {
    F x := P.F x + Q.F x
    isEq := by simp [P.isEqAt, Q.isEqAt] }

end Polynomial

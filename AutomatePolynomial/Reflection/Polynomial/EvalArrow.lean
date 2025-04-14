import AutomatePolynomial.Reflection.Polynomial.Defs

/-!
# *Implementation*: Evaluation Lambdas

 -/

namespace Polynomial.Rfl

variable [CommSemiring R]

/-- A lambda representation of polynomial evaluations -/
abbrev EvalArrow :=
  Eval (fun _ => R → R) (fun _ F => F)

/-- A reflection system for `Eval` using the `EvalArrow` representation -/
instance instEvalArrowReflection :
    EvalReflection R (fun _ => R → R) (fun _ F => F) where

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

  mk_pow n P := {
    F x := P.F x ^ n
    isEq := by simp[P.isEqAt] }

  mk_mul P Q := {
    F x := P.F x * Q.F x
    isEq := by simp[P.isEqAt, Q.isEqAt] }

  mk_add P Q := {
    F x := P.F x + Q.F x
    isEq := by simp[P.isEqAt, Q.isEqAt] }

end Polynomial.Rfl

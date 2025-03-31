import AutomatePolynomial.Reflection.Polynomial.Defs

namespace Polynomial

variable [Semiring R]

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
    isEq := by sorry }

  mk_pow _ n P := {
    F x := P.F x ^ n
    isEq := by sorry }

  mk_mul _ _ P Q := {
    F x := P.F x * Q.F x
    isEq := by sorry }

  mk_add _ _ P Q := {
    F x := P.F x + Q.F x
    isEq := by sorry }

end Polynomial

/-
namespace Polynomial

-- compute polynomial evaluation
variable [Semiring R] in
class Eval (p : R[X]) where
  f : R → R
  isEq : p.eval = f

-- apply equality proof of evaluation at specific point
variable [Semiring R] in
lemma Eval.isEqAt [Eval p] (x : R) :
    p.eval x = Eval.f p x :=
  Eval.isEq.rec rfl

section Eval

-- the zero polynomial evaluates to 0
variable [Semiring R] in
@[simp]
instance instEvalZero : Eval (0 : R[X]) where
  f := 0
  isEq := funext (fun _ => eval_zero)

-- the one polynomial evaluates to 1
variable [Semiring R] in
@[simp]
instance instEvalOne : Eval (1 : R[X]) where
  f := 1
  isEq := funext (fun _ => eval_one)

-- a constant polynomial evaluates to a constant
variable [Semiring R] in
@[simp]
instance instEvalC : Eval (C c : R[X]) where
  f _ := c
  isEq := funext (fun _ => eval_C)

-- the identity polynomial evaluates to the identity
variable [Semiring R] in
@[simp]
instance instEvalX : Eval (X : R[X]) where
  f x := x
  isEq := funext (fun _ => eval_X)

-- evaluation of the power of polynomial
-- given the evaluations of the polynomial
variable [CommSemiring R] (p : R[X]) [Eval p] in
@[simp]
instance instEvalPow : Eval (p ^ n) where
  f := Eval.f p ^ n
  isEq := Eval.isEq.rec (funext (fun _ => eval_pow n))

-- evaluation of the sum of polynomials
-- given the evaluations of the polynomials
variable [CommSemiring R] (p q : R[X]) [Eval p] [Eval q] in
@[simp]
instance instEvalMul : Eval (p * q) where
  f := Eval.f p * Eval.f q
  isEq := Eval.isEq.rec (Eval.isEq.rec (funext (fun _ => eval_mul)))

-- evaluation of the sum of polynomials
-- given the evaluations of the polynomials
variable [Semiring R] (p q : R[X]) [Eval p] [Eval q] in
@[simp]
instance instEvalAdd : Eval (p + q) where
  f := Eval.f p + Eval.f q
  isEq := Eval.isEq.rec (Eval.isEq.rec (funext (fun _ => eval_add)))

end Eval

end Polynomial
-/

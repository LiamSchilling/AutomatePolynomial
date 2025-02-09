import AutomatePolynomial.Polynomial
import AutomatePolynomial.WithBot

namespace Polynomial

variable {R : Type*} [Semiring R]
variable (n : ℕ) (c : R) (p q : R[X])

-- compute polynomial evaluation
class Eval (p : R[X]) where
  f : R → R
  isEq : p.eval = f

-- apply equality proof of evaluation at specific point
lemma Eval.isEqAt {p : R[X]} [Eval p] : p.eval c = Eval.f p c :=
  Eval.isEq.rec rfl

section Eval

variable [Eval p] [Eval q]

-- the zero polynomial evaluates to 0
instance instEvalZero : Eval (0 : R[X]) where
  f := 0
  isEq := funext (fun _ => eval_zero)

-- the one polynomial evaluates to 1
instance instEvalOne : Eval (1 : R[X]) where
  f := 1
  isEq := funext (fun _ => eval_one)

-- a constant polynomial evaluates to a constant
instance instEvalC : Eval (C c : R[X]) where
  f := fun _ => c
  isEq := funext (fun _ => eval_C)

-- the identity polynomial evaluates to the identity
instance instEvalX : Eval (X : R[X]) where
  f := fun x => x
  isEq := funext (fun _ => eval_X)

-- evaluation of the sum of polynomials
-- given the evaluations of the polynomials
instance instEvalAdd : Eval (p + q) where
  f := Eval.f p + Eval.f q
  isEq := Eval.isEq.rec (Eval.isEq.rec (funext (fun _ => eval_add)))

end Eval

end Polynomial

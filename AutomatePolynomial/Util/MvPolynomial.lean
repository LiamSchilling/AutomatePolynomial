import Mathlib.Algebra.MvPolynomial.Variables
import AutomatePolynomial.Util.Hyperlist

--namespace MvPolynomial

variable [CommSemiring R] [LinearOrder σ]

/-
-- given coefficients
-- [ ... [ [ c###MK, ... c###M0 ], ... [ c###0K, c###00 ] ] ... ]
-- computes abstract polynomial
-- ( ... #^# * ( ( c###00 + ... k^K * c###0K ) + ... m^M * ( c###M0 + ... k^K * c###MK ) ) ... )
noncomputable def MvCoeffs.expandAux :
  (is : List σ) → (cs : Hyperlist R is.length) →
  (n : Option ℕ) → cs.length = n → MvPolynomial σ R
| [], cs, _, _ => C cs
| i :: is, [], _, _ => 0
| i :: is, c :: cs, none, _ => by contradiction
| i :: is, c :: cs, some n, h =>
  expandAux (i :: is) cs (some n.pred) (
    Option.some_inj.mpr (
      Nat.pred_eq_of_eq_succ (Option.some_inj.mp h).symm ).symm ) +
  X i ^ n.pred * expandAux is c c.length rfl
termination_by is cs => (is.length, cs.length)
decreasing_by
. apply Prod.Lex.right; apply lt_add_one
. apply Prod.Lex.left; simp

end MvPolynomial

-- fully unfold expand call
syntax "unfold_mv_expand_aux" : tactic
macro_rules
  | `(tactic| unfold_mv_expand_aux) =>
    `(tactic| repeat unfold MvPolynomial.MvCoeffs.expandAux; try simp only [Hyperlist.length, List.length])
-/

import AutomatePolynomial.Hyperlist.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Lemmas

namespace Polynomial.Coeffs

variable [Semiring R]

-- add coefficient lists
@[simp]
def addAux (cs1 cs2 : List R) :=
  List.match_zipWith (. + .) cs1 cs2 0 0

lemma addAux_eq
    {n : ℕ} {cs1 cs2 : List R} :
    (addAux cs1 cs2)[n]?.getD 0 =
    cs1[n]?.getD 0 + cs2[n]?.getD 0 := by
  nth_rw 1 [←show 0 + 0 = (0 : R) by simp]
  apply List.getElem?_getD_match_zipWith

-- multiply coefficient lists
@[simp]
def mulAux (cs1 cs2 : List R) :=
  match cs1 with
  | [] => List.replicate cs2.length 0
  | c :: cs1 => addAux (0 :: mulAux cs1 cs2) (cs2.map (c * .))

-- power of a coefficient list
@[simp]
def powAux (n : ℕ) (cs : List R) :=
  match n with
  | 0 => [1]
  | n + 1 => mulAux (powAux n cs) cs

-- given coefficients [c0, c1, ... cn]
-- computes abstract polynomial (cn*x^n + ... c1*x + c0)
noncomputable def expandAux (cs : List R) (n : ℕ) :=
  match cs with
  | [] => 0
  | c :: cs => expandAux cs n.succ + C c * X ^ n

end Polynomial.Coeffs

-- fully unfold expand call
syntax "unfold_expand_aux" : tactic
macro_rules
  | `(tactic| unfold_expand_aux) =>
    `(tactic| repeat unfold Polynomial.Coeffs.expandAux)

import AutomatePolynomial.Hyperlist.Lemmas
import Mathlib.Algebra.MvPolynomial.Variables

/-!
# *Representation*: Coefficient Hyperlists

We use `Hyperlist`,
along with a `List` labeling dimensions by variable names,
as a dense representation of multivariate polynomial coefficients.

 -/

namespace MvPolynomial.CoeffHyperlist

variable [LinearOrder σ] [CommSemiring R]

/-- Coefficient list operation corresponding to polynomial addition -/
@[simp]
def add (I1 I2 : List σ) (L1 L2 : Hyperlist R) :=
  Hyperlist.nodupsMerge_zipWithPad (. + .) 0 0 I1 I2 L1 L2

/-- Coefficient list operation corresponding to polynomial multiplication by a constant -/
@[simp]
def mulC (c : R) (L : Hyperlist R) :=
  Hyperlist.map (c * .) L

/-- Coefficient list operation corresponding to polynomial multiplication by `X i`
where `i` exactly the first variable label in the polynomial -/
@[simp]
def mulXHead (L : Hyperlist R) :=
  Hyperlist.list (Hyperlist.single 0 :: L.toList)

/-- Coefficient list operation corresponding to polynomial multiplication by `X i`
where `i` is less than every other variable label in the polynomial -/
@[simp]
def mulXNew (L : Hyperlist R) :=
  Hyperlist.list [L]

/-- TODO: CLEAN & DOCSTRING

given coefficients
[ ... [ [ c###00, ... c###0K ], ... [ c###M0, c###MK ] ] ... ]
computes abstract polynomial
( ... #^# * ( m^M * ( k^K * c###MK + ... c###M0 ) + ... ( k^K * c###0K + ... c###00 ) ) ... ) -/
noncomputable def expandAux (is : List σ) (cs : Hyperlist R) (n : ℕ) : MvPolynomial α R :=
  sorry
--  match is, cs with
--  | [], .mk c _ => C c
--  | i :: is, .mk c .nil => X i ^ n * expandAux is (.mk c .nil) 0
--  | i :: is, .mk c (.node c_ TL DM) => expandAux (i :: is) (.mk c_ TL) n.succ + X i ^ n * expandAux is (.mk c DM) 0

syntax "unfold_mv_expand_aux" : tactic
macro_rules
  | `(tactic| unfold_mv_expand_aux) =>
    `(tactic| repeat unfold MvPolynomial.CoeffHyperlist.expandAux)

end MvPolynomial.CoeffHyperlist

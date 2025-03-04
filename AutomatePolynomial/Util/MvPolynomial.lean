import AutomatePolynomial.Util.Hyperlist
import Mathlib.Algebra.MvPolynomial.Variables

namespace MvPolynomial.MvCoeffs

variable [CommSemiring R] [LinearOrder σ]

-- add coefficient lists
@[simp]
def addAux (is1 is2 : List σ) (cs1 cs2 : Hyperlist R) :=
  Hyperlist.merge_and_match_zipWith (. + .)  is1 is2 cs1 cs2 0 0

-- given coefficients
-- [ ... [ [ c###00, ... c###0K ], ... [ c###M0, c###MK ] ] ... ]
-- computes abstract polynomial
-- ( ... #^# * ( m^M * ( k^K * c###MK + ... c###M0 ) + ... ( k^K * c###0K + ... c###00 ) ) ... )
noncomputable def expandAux (is : List σ) (cs : Hyperlist R) (n : ℕ) :=
  match is, cs with
  | [], .mk c _ => C c
  | i :: is, .mk c .nil => X i ^ n * expandAux is (.mk c .nil) 0
  | i :: is, .mk c (.node c_ TL DM) => expandAux (i :: is) (.mk c_ TL) n.succ + X i ^ n * expandAux is (.mk c DM) 0

end MvPolynomial.MvCoeffs

-- fully unfold expand call
syntax "unfold_mv_expand_aux" : tactic
macro_rules
  | `(tactic| unfold_mv_expand_aux) =>
    `(tactic| repeat unfold MvPolynomial.MvCoeffs.expandAux)

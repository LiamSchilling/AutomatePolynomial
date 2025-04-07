import AutomatePolynomial.Hyperlist.Lemmas
import Mathlib.Algebra.MvPolynomial.Variables

namespace MvPolynomial.MvCoeffs

variable [CommSemiring R] [LinearOrder σ]

-- add coefficient lists
@[simp]
def addAux (is1 is2 : List σ) (cs1 cs2 : Hyperlist R) :=
  Hyperlist.merge_and_match_zipWith (. + .)  is1 is2 cs1 cs2 0 0

-- multiply by constant
@[simp]
def mulCAux (c : R) (cs : Hyperlist R) :=
  cs.map (c * .)

-- multiply by X i if i is the first dimension in cs
@[simp]
def mulXHeadAux [Zero R] (cs : Hyperlist R) :=
  Hyperlist.node (some cs) (Hyperlist.mk 0 .nil)

-- multiply by X i if i is less than all dimensions in cs
def mulXNewAux [Zero R] (cs : Hyperlist R) :=
  Hyperlist.node (some (Hyperlist.mk 0 .nil)) cs

-- multiply coefficient lists
@[simp]
def mulAux [Zero R] (is1 is2 : List σ) (cs1 cs2 : Hyperlist R) :=
  match is1, is2 with
  | [], [] => Hyperlist.mk (cs1.get_head * cs2.get_head) .nil
  | [], _ :: is2 =>
    match cs2 with
    | Hyperlist.mk c .nil => mulCAux c cs1
    | Hyperlist.mk c (.node c_ T1 T2) => addAux is1 is2 (mulXHeadAux (mulCAux c_ cs1)) (mulXNewAux (mulAux [] is2 (mulXNewAux (mulCAux c_ cs1)) (Hyperlist.mk c T2)))
  | _ :: is1, [] =>
    match cs1 with
    | Hyperlist.mk c .nil => mulCAux c cs2
    | Hyperlist.mk c (.node c_ T1 T2) => addAux is1 is2 (mulXHeadAux (mulCAux c_ cs1)) (mulXNewAux (mulAux is1 [] (mulXNewAux (mulCAux c_ cs1)) (Hyperlist.mk c T2)))
  | i1 :: is1, i2 :: is2 =>
  match cmp i1 i2 with
  | .lt => sorry
  | .gt => sorry
  | .eq => sorry

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

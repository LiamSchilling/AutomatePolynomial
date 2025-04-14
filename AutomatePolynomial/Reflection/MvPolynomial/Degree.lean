import AutomatePolynomial.Reflection.MvPolynomial.Defs

/-!
# *Implementation*: Weighted Total Degree

 -/

namespace MvPolynomial.Rfl

variable {σ : Type*} [CommSemiring R]
variable [AddCommMonoid M] [SemilatticeSup M] [OrderBot M]

/-- A reflection system for `MvWeightedTotalDegreeLe` -/
instance instMvWeightedTotalDegreeLeReflection (w : σ → M) :
    MvWeightedTotalDegreeLeReflection σ R w where

  mk_zero := {
    D := 0
    isLe := sorry }

  mk_C _ := {
    D := 0
    isLe := sorry }

  mk_X j := {
    D := w j
    isLe := sorry }

  mk_XPow j n := {
    D := n • w j
    isLe := sorry }

  mk_pow n P := {
    D := n • P.D
    isLe := sorry }

  mk_mul P Q := {
    D := P.D + Q.D
    isLe := sorry }

  mk_add P Q := {
    D := max P.D Q.D
    isLe := sorry }

end MvPolynomial.Rfl

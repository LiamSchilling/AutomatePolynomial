import AutomatePolynomial.Reflection.MvPolynomial.Defs

namespace MvPolynomial

variable [CommSemiring R]
variable [AddCommMonoid M] [SemilatticeSup M] [OrderBot M]

instance instMvTotalDegreeLeReflection (w : σ → M) : MvWeightedTotalDegreeLeReflection σ R w where

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

  mk_pow _ n P := {
    D := n • P.D
    isLe := sorry }

  mk_mul _ _ P Q := {
    D := P.D + Q.D
    isLe := sorry }

  mk_add _ _ P Q := {
    D := max P.D Q.D
    isLe := sorry }

end MvPolynomial

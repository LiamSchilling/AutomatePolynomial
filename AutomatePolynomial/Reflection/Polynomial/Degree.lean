import AutomatePolynomial.Reflection.Polynomial.Defs

/-!
# *Implementation*: Degrees and Leading Coefficients

 -/

namespace Polynomial.Rfl

variable [Semiring R]

/- A reflection system for `DegreeLe` -/
instance instDegreeLeReflection :
    DegreeLeReflection R where

  mk_zero := {
    D := ⊥
    isLe := C_0.symm.rec (le_of_eq degree_zero) }

  mk_C _ := {
    D := 0
    isLe := degree_C_le }

  mk_X := {
    D := 1
    isLe := degree_X_le }

  mk_XPow n := {
    D := n
    isLe := degree_X_pow_le n }

  mk_pow n P := {
    D := n * P.D
    isLe := degree_pow_le_of_le n P.isLe }

  mk_mul P Q := {
    D := P.D + Q.D
    isLe := degree_mul_le_of_le P.isLe Q.isLe }

  mk_add P Q := {
    D := max P.D Q.D
    isLe := degree_add_le_of_le P.isLe Q.isLe }

/- A reflection system for `DegreeEq` -/
instance instDegreeEqReflection :
    DegreeEqReflection R where

  mk_zero := {
    D := ⊥
    isEq := C_0.symm.rec degree_zero }

  mk_C _ h := {
    D := 0
    isEq := degree_C h }

  mk_X := {
    D := 1
    isEq := degree_X }

  mk_XPow n := {
    D := n
    isEq := degree_X_pow n }

  mk_pow n h P := {
    D := n • P.D
    isEq := P.isEq.rec (degree_pow' h) }

  mk_mul h P Q := {
    D := P.D + Q.D
    isEq := P.isEq.rec (Q.isEq.rec (degree_mul' h)) }

  mk_add_left h P := {
    D := P.D
    isEq := P.isEq.rec (degree_add_eq_left_of_degree_lt h) }

  mk_add_right h Q := {
    D := Q.D
    isEq := Q.isEq.rec (degree_add_eq_right_of_degree_lt h) }

  mk_add_bal h1 h2 P _ := {
    D := P.D
    isEq :=
      P.isEq.rec (Eq.trans
        (degree_add_eq_of_leadingCoeff_add_ne_zero h2)
        (max_eq_left (le_of_eq h1.symm)) ) }

/- A reflection system for `LeadingCoeff` -/
instance instLeadingCoeffRefelction :
    LeadingCoeffReflection R where

  mk_zero := {
    c := 0
    isEq := leadingCoeff_C 0 }

  mk_C c := {
    c := c
    isEq := leadingCoeff_C c }

  mk_X := {
    c := 1
    isEq := leadingCoeff_X }

  mk_XPow n := {
    c := 1
    isEq := Monic.leadingCoeff (monic_X_pow n) }

  mk_pow n h P := {
    c := P.c ^ n
    isEq := P.isEq.rec (leadingCoeff_pow' h) }

  mk_mul h P Q := {
    c := P.c * Q.c
    isEq := P.isEq.rec (Q.isEq.rec (leadingCoeff_mul' h)) }

  mk_add_left h P := {
    c := P.c
    isEq := P.isEq.rec (leadingCoeff_add_of_degree_lt' h) }

  mk_add_right h Q := {
    c := Q.c
    isEq := Q.isEq.rec (leadingCoeff_add_of_degree_lt h) }

  mk_add_bal h1 h2 P Q := {
    c := P.c + Q.c
    isEq := P.isEq.rec (Q.isEq.rec (leadingCoeff_add_of_degree_eq h1 h2)) }

end Polynomial.Rfl

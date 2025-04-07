import AutomatePolynomial.Reflection.Polynomial.Defs

namespace Polynomial

variable [Semiring R]

instance instDegreeLeReflection : DegreeLeReflection R where

  mk_zero := {
    D := ⊥
    isLe := C_0.symm.rec ((degree_le_iff_coeff_zero 0 ⊥).mpr (fun _ => congrFun rfl)) }

  mk_C _ := {
    D := 0
    isLe := degree_C_le }

  mk_X := {
    D := 1
    isLe := degree_X_le }

  mk_XPow n := {
    D := n
    isLe :=
      le_trans (
        degree_pow_le_of_le n degree_X_le ) (
        le_of_eq (mul_one _) ) }

  mk_pow _ n P := {
    D := n * P.D
    isLe := degree_pow_le_of_le n P.isLe }

  mk_mul _ _ P Q := {
    D := P.D + Q.D
    isLe := degree_mul_le_of_le P.isLe Q.isLe }

  mk_add _ _ P Q := {
    D := max P.D Q.D
    isLe := degree_add_le_of_le P.isLe Q.isLe }

instance instDegreeEqReflection : DegreeEqReflection R where

  mk_zero := {
    D := ⊥
    isEq := C_0.symm.rec degree_zero }

  mk_C c := {
    D := 0
    isEq := degree_C (NeZero.ne c) }

  mk_X := {
    D := 1
    isEq := degree_X }

  mk_XPow n := {
    D := n
    isEq :=
      Eq.trans (
        degree_pow' (
          leadingCoeff_X.symm.rec (
            (one_pow n).symm.rec one_ne_zero ) ) ) (
        degree_X.symm.rec ((nsmul_eq_mul n 1).symm.rec (mul_one _)) ) }

  mk_pow p _ n _ P := {
    D := n • P.D
    isEq :=
      DegreeEq.isEq.rec (degree_pow' (
        LeadingCoeff.isEq.symm.rec (
          NeZero.ne (leadingCoeffPow p n) ) )) }

  mk_mul p q _ _ _ P Q := {
    D := P.D + Q.D
    isEq :=
      DegreeEq.isEq.rec (DegreeEq.isEq.rec (degree_mul' (
        LeadingCoeff.isEq.symm.rec (LeadingCoeff.isEq.symm.rec (
          NeZero.ne (leadingCoeffMul p q) )) ))) }

  mk_add_left p q P Q h _ _ := {
    D := P.D
    isEq := by
      revert P Q; intro P Q h; exact
      DegreeEq.isEq.rec (degree_add_eq_left_of_degree_lt (
        apply_degreeLt h )) }

  mk_add_right p q P Q h _ _ := {
    D := Q.D
    isEq := by
      revert P Q; intro P Q h; exact
      DegreeEq.isEq.rec (degree_add_eq_right_of_degree_lt (
        apply_degreeLt h )) }

  mk_add_balanced p q P Q _ _ neqz h _ _ := {
    D := P.D
    isEq := by
      revert P Q; intro P Q h
      rw[←DegreeEq.isEq]
      rw[degree_add_eq_of_leadingCoeff_add_ne_zero, apply_degreeEq h]; simp
      rw[LeadingCoeff.isEq, LeadingCoeff.isEq]; apply neqz.ne }

instance instLeadingCoeffRefelction : LeadingCoeffReflection R where

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

  mk_pow p P n _ _ := {
    c := P.c ^ n
    isEq := by
      revert P; intro P _; exact
      LeadingCoeff.isEq.rec (leadingCoeff_pow' (
        LeadingCoeff.isEq.symm.rec (
          NeZero.ne (leadingCoeffPow p n) ) )) }

  mk_mul p q P Q _ _ _ := {
    c := P.c * Q.c
    isEq := by
      revert P Q; intro P Q _; exact
      LeadingCoeff.isEq.rec (LeadingCoeff.isEq.rec (leadingCoeff_mul' (
        LeadingCoeff.isEq.symm.rec (LeadingCoeff.isEq.symm.rec (
          NeZero.ne (leadingCoeffMul p q) )) ))) }

  mk_add_left p q _ _ h P Q := {
    c := P.c
    isEq :=
      by revert P Q; intro P Q; exact
      LeadingCoeff.isEq.rec (leadingCoeff_add_of_degree_lt' (
        apply_degreeLt h )) }

  mk_add_right p q _ _ h P Q := {
    c := Q.c
    isEq :=
      by revert P Q; intro P Q; exact
      LeadingCoeff.isEq.rec (leadingCoeff_add_of_degree_lt (
        apply_degreeLt h )) }

  mk_add_balanced p q _ _ P Q _ h _ _ := {
    c := P.c + Q.c
    isEq :=
      by revert P Q; intro P Q _; exact
      LeadingCoeff.isEq.rec (LeadingCoeff.isEq.rec (
        leadingCoeff_add_of_degree_eq (apply_degreeEq h) (
          LeadingCoeff.isEq.symm.rec (LeadingCoeff.isEq.symm.rec (
            NeZero.ne (leadingCoeffAdd p q) )) ) )) }

end Polynomial

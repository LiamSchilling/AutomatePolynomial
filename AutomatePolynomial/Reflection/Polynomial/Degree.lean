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

  mk_add_left p q _ _ _ P Q := {
    D := P.D
    isEq := sorry }

  mk_add_right p q _ _ _ P Q := {
    D := Q.D
    isEq := sorry }

  mk_add_balanced p q _ _ _ _ _ h P Q := {
    D := P.D
    isEq := sorry }

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
    isEq :=
      Eq.trans (
        show _ = X.leadingCoeff ^ n by sorry ) (
        leadingCoeff_X.symm.rec (one_pow n) ) }

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

/-
namespace Polynomial

variable [Semiring R] [Nontrivial R]

-- compute greedy upper bound on polynomial degree
class DegreeLe (p : R[X]) where
  D : WithBot ℕ
  isLe : p.degree ≤ D

-- compute exact polynomial degree
class DegreeEq (p : R[X]) where
  D : WithBot ℕ
  isEq : p.degree = D

-- compute polynomial leading coefficient
class LeadingCoeff (p : R[X]) where
  c : R
  isEq : p.leadingCoeff = c

-- degree of p is definitely less than degree of q
@[simp]
def degreeLt (p q : R[X]) [DegreeLe p] [DegreeEq q] :=
  DegreeLe.D p < DegreeEq.D q

-- degree of p is definitely equal to degree of q
@[simp]
def degreeEq (p q : R[X]) [DegreeEq p] [DegreeEq q] :=
  DegreeEq.D p = DegreeEq.D q

-- power of leading coefficient
@[simp]
def leadingCoeffPow (p : R[X]) (n : ℕ) [LeadingCoeff p] :=
  LeadingCoeff.c p ^ n

-- product of leading coefficients
@[simp]
def leadingCoeffMul (p q : R[X]) [LeadingCoeff p] [LeadingCoeff q] :=
  LeadingCoeff.c p * LeadingCoeff.c q

-- sum of leading coefficients
@[simp]
def leadingCoeffAdd (p q : R[X]) [LeadingCoeff p] [LeadingCoeff q] :=
  LeadingCoeff.c p + LeadingCoeff.c q

-- useful meaning of the computable degree comparison
omit [Nontrivial R] in
variable {p q : R[X]} [DegreeEq q] [DegreeLe p] in
lemma apply_degreeLt (h : degreeLt p q) : p.degree < q.degree :=
  lt_of_le_of_lt (DegreeLe.isLe) (DegreeEq.isEq.symm.rec h)

-- useful meaning of the computable degree equality
omit [Nontrivial R] in
variable {p q : R[X]} [DegreeEq p] [DegreeEq q] in
lemma apply_degreeEq (h : degreeEq p q) : p.degree = q.degree :=
  DegreeEq.isEq.symm.rec (DegreeEq.isEq.symm.rec h)

-- exact degree implies upper bound on degree
@[simp]
def degreeLe_of_degreeEq (p : R[X]) [DegreeEq p] : DegreeLe p where
  D := DegreeEq.D p
  isLe := DegreeEq.isEq.rec (WithBot.le_self (fun _ => le_of_eq rfl))

section DegreeLe

-- the zero polynomial has degree at most ⊥
@[simp]
instance instDegreeLeZero : DegreeLe (0 : R[X]) where
  D := ⊥
  isLe :=
    (degree_le_iff_coeff_zero 0 ⊥).mpr (fun _ => congrFun rfl)

-- the one polynomial has degree at most 0
@[simp]
instance instDegreeLeOne : DegreeLe (1 : R[X]) where
  D := 0
  isLe := degree_one_le

-- the zero constant polynomial has degree at most ⊥
@[simp]
instance instDegreeLeCZero : DegreeLe (C 0 : R[X]) where
  D := ⊥
  isLe :=
    C_0.symm.rec (degree_le_iff_coeff_zero 0 ⊥).mpr (fun _ => congrFun rfl)

-- a constant polynomial has degree at most 0
@[simp]
instance instDegreeLeC : DegreeLe (C c : R[X]) where
  D := 0
  isLe := degree_C_le

-- the identity polynomial has degree at most 1
@[simp]
instance instDegreeLeX : DegreeLe (X : R[X]) where
  D := 1
  isLe := degree_X_le

-- compute upper bound of the power of a polynomial
-- given upper bound of the polynomial
variable (p : R[X]) [DegreeLe p] in
@[simp]
instance instDegreeLePow : DegreeLe (p ^ n) where
  D := n * DegreeLe.D p
  isLe := degree_pow_le_of_le n DegreeLe.isLe

-- compute upper bound of the product of polynomials
-- given the upper bound of the polynomials
variable (p q : R[X]) [DegreeLe p] [DegreeLe q] in
@[simp]
instance instDegreeLeMul : DegreeLe (p * q) where
  D := DegreeLe.D p + DegreeLe.D q
  isLe := degree_mul_le_of_le DegreeLe.isLe DegreeLe.isLe

-- compute upper bound of the sum of polynomials
-- given the upper bound of the polynomials
variable (p q : R[X]) [DegreeLe p] [DegreeLe q] in
@[simp]
instance instDegreeLeAdd : DegreeLe (p + q) where
  D := max (DegreeLe.D p) (DegreeLe.D q)
  isLe := degree_add_le_of_le DegreeLe.isLe DegreeLe.isLe

end DegreeLe

section DegreeEq

-- the zero polynomial has degree ⊥
@[simp]
instance instDegreeEqZero : DegreeEq (0 : R[X]) where
  D := ⊥
  isEq := degree_zero

-- the one polynomial over nontrivial types has degree 0
@[simp]
instance instDegreeEqOne : DegreeEq (1 : R[X]) where
  D := 0
  isEq := degree_one

-- the zero constant polynomial has degree ⊥
@[simp]
instance instDegreeEqCZero : DegreeEq (C 0 : R[X]) where
  D := ⊥
  isEq := leadingCoeff_eq_zero_iff_deg_eq_bot.mp (leadingCoeff_C 0)

-- a nonzero constant polynomial has degree 0
variable {c : R} [NeZero c] in
@[simp]
instance instDegreeEqCNonzero : DegreeEq (C c : R[X]) where
  D := 0
  isEq := degree_C (NeZero.ne c)

-- compute constant polynomial degree
-- given decidability of whether the constant is zero
variable [DecidablePred (Eq 0 : R → Prop)] in
@[simp]
instance instDegreeEqC : DegreeEq (C c : R[X]) :=
  match inferInstanceAs (Decidable (0 = c)) with
  | isFalse h => @instDegreeEqCNonzero _ _ _ ⟨fun hn => h hn.symm⟩
  | isTrue h => h.rec instDegreeEqCZero

-- the identity polynomial over nontrivial types has degree 1
@[simp]
instance instDegreeEqX : DegreeEq (X : R[X]) where
  D := 1
  isEq := degree_X

-- compute degree of power given leading coefficient does not become zero
variable (p : R[X]) [DegreeEq p] in
variable [LeadingCoeff p] [NeZero (leadingCoeffPow p n)] in
@[simp]
instance instDegreeEqPowOfLeadingCoeff : DegreeEq (p ^ n) where
  D := n • DegreeEq.D p
  isEq :=
    DegreeEq.isEq.rec (degree_pow' (
      LeadingCoeff.isEq.symm.rec (
        NeZero.ne (leadingCoeffPow p n) ) ))

-- compute degree of product given leading coefficient does not become zero
variable (p q : R[X]) [DegreeEq p] [DegreeEq q] in
variable [LeadingCoeff p] [LeadingCoeff q] [NeZero (leadingCoeffMul p q)] in
@[simp]
instance instDegreeEqMulOfLeadingCoeff : DegreeEq (p * q) where
  D := DegreeEq.D p + DegreeEq.D q
  isEq :=
    DegreeEq.isEq.rec (DegreeEq.isEq.rec (degree_mul' (
      LeadingCoeff.isEq.symm.rec (LeadingCoeff.isEq.symm.rec (
        NeZero.ne (leadingCoeffMul p q) )) )))

-- compute degree of sum where left side has greater degree
variable (p q : R[X]) [DegreeEq p] [DegreeLe q] (h : degreeLt q p) in
variable [LeadingCoeff p] in
@[simp]
instance instDegreeEqAddLeft : DegreeEq (p + q) where
  D := DegreeEq.D p
  isEq :=
    have _ := DegreeLe.D q
    have _ := h
    sorry

-- compute degree of sum where right side has greater degree
variable (p q : R[X]) [DegreeEq q] [DegreeLe p] (h : degreeLt p q) in
variable [LeadingCoeff q] in
@[simp]
instance instDegreeEqAddRight : DegreeEq (p + q) where
  D := DegreeEq.D q
  isEq :=
    have _ := DegreeLe.D p
    have _ := h
    sorry

-- compute degree of sum where sides have same degree
variable (p q : R[X]) [DegreeEq p] [DegreeEq q] (h : degreeEq p q) in
variable [LeadingCoeff p] [LeadingCoeff q] [NeZero (leadingCoeffAdd p q)] in
@[simp]
def degreeEq_add_balanced_of_leadingCoeff : DegreeEq (p + q) where
  D := DegreeEq.D p
  isEq :=
    have _ := DegreeEq.D q
    have _ := h
    have _ := LeadingCoeff.c p
    have _ := LeadingCoeff.c q
    have _ := NeZero.ne (leadingCoeffAdd p q)
    sorry

-- compute degree of sum given leading coeff inequality
variable (p q : R[X]) [DegreeEq p] [DegreeEq q] in
variable [LeadingCoeff p] [LeadingCoeff q] [NeZero (leadingCoeffAdd p q)] in
@[simp]
instance instDegreeEqAddOfLeadingCoeff : DegreeEq (p + q) :=
  match h : compare (DegreeEq.D p) (DegreeEq.D q) with
  | Ordering.gt =>
    @instDegreeEqAddLeft _ _ _ _ _
      (degreeLe_of_degreeEq q)
      ((compare_iff _ _).mp h)
  | Ordering.lt =>
    @instDegreeEqAddRight _ _ _ _ _
      (degreeLe_of_degreeEq p)
      ((compare_iff _ _).mp h)
  | Ordering.eq =>
    degreeEq_add_balanced_of_leadingCoeff _ _
      ((compare_iff _ _).mp h)

end DegreeEq

section LeadingCoeff

-- the zero polynomial has leading coefficient 0
@[simp]
instance instLeadingCoeffZero : LeadingCoeff (0 : R[X]) where
  c := 0
  isEq := leadingCoeff_zero

-- the one polynomial has leading coefficient 1
@[simp]
instance instLeadingCoeffOne : LeadingCoeff (1 : R[X]) where
  c := 1
  isEq := leadingCoeff_one

-- the constant c polynomial has leading coefficient c
@[simp]
instance instLeadingCoeffC : LeadingCoeff (C c : R[X]) where
  c := c
  isEq := leadingCoeff_C c

-- the identity polynomial has leading coefficient 1
@[simp]
instance instLeadingCoeffX : LeadingCoeff (X : R[X]) where
  c := 1
  isEq := leadingCoeff_X

-- compute leading coefficient of the power of a polynomial
-- given the leading coefficient of the polynomial
-- given the result is nonzero
variable (p : R[X]) in
variable [LeadingCoeff p] [NeZero (leadingCoeffPow p n)] in
@[simp]
instance instLeadingCoeffPow : LeadingCoeff (p ^ n) where
  c := LeadingCoeff.c p ^ n
  isEq :=
    LeadingCoeff.isEq.rec (leadingCoeff_pow' (
      LeadingCoeff.isEq.symm.rec (
        NeZero.ne (leadingCoeffPow p n) ) ))

-- compute leading coefficient of the product of polynomials
-- given the leading coefficient of the polynomials
-- given the result is nonzero
variable (p q : R[X]) in
variable [LeadingCoeff p] [LeadingCoeff q] [NeZero (leadingCoeffMul p q)] in
@[simp]
instance instLeadingCoeffMul : LeadingCoeff (p * q) where
  c := LeadingCoeff.c p * LeadingCoeff.c q
  isEq :=
    LeadingCoeff.isEq.rec (LeadingCoeff.isEq.rec (leadingCoeff_mul' (
      LeadingCoeff.isEq.symm.rec (LeadingCoeff.isEq.symm.rec (
        NeZero.ne (leadingCoeffMul p q) )) )))

-- compute leading coefficient of sum where left side has greater degree
variable (p q : R[X]) [DegreeEq p] [DegreeLe q] (h : degreeLt q p) in
variable [LeadingCoeff p] in
@[simp]
instance instLeadingCoeffAddLeft : LeadingCoeff (p + q) where
  c := LeadingCoeff.c p
  isEq :=
    LeadingCoeff.isEq.rec (leadingCoeff_add_of_degree_lt' (
      apply_degreeLt h ))

-- compute leading coefficient of sum where right side has greater degree
variable (p q : R[X]) [DegreeEq q] [DegreeLe p] (h : degreeLt p q) in
variable [LeadingCoeff q] in
@[simp]
instance instLeadingCoeffAddRight : LeadingCoeff (p + q) where
  c := LeadingCoeff.c q
  isEq :=
    LeadingCoeff.isEq.rec (leadingCoeff_add_of_degree_lt (
      apply_degreeLt h ))

-- compute leading coefficient of sum where sides have same degree
variable (p q : R[X]) [DegreeEq p] [DegreeEq q] (h : degreeEq p q) in
variable [LeadingCoeff p] [LeadingCoeff q] [NeZero (leadingCoeffAdd p q)] in
@[simp]
def leadingCoeff_add_balanced_of_degreeEq : LeadingCoeff (p + q) where
  c := LeadingCoeff.c p + LeadingCoeff.c q
  isEq :=
    LeadingCoeff.isEq.rec (LeadingCoeff.isEq.rec (
      leadingCoeff_add_of_degree_eq (apply_degreeEq h) (
        LeadingCoeff.isEq.symm.rec (LeadingCoeff.isEq.symm.rec (
          NeZero.ne (leadingCoeffAdd p q) )) ) ))

-- compute leading coefficient of sum given both degrees
variable (p q : R[X]) [DegreeEq p] [DegreeEq q] in
variable [LeadingCoeff p] [LeadingCoeff q] [NeZero (leadingCoeffAdd p q)] in
@[simp]
instance instLeadingCoeffAddOfDegreeEq : LeadingCoeff (p + q) :=
  match h : compare (DegreeEq.D p) (DegreeEq.D q) with
  | Ordering.gt =>
    @instLeadingCoeffAddLeft _ _ _ _ _
      (degreeLe_of_degreeEq q)
      ((compare_iff _ _).mp h) _
  | Ordering.lt =>
    @instLeadingCoeffAddRight _ _ _ _ _
      (degreeLe_of_degreeEq p)
      ((compare_iff _ _).mp h) _
  | Ordering.eq =>
    leadingCoeff_add_balanced_of_degreeEq _ _
      ((compare_iff _ _).mp h)

end LeadingCoeff

end Polynomial
-/

import AutomatePolynomial.Util.Polynomial
import AutomatePolynomial.Util.WithBot

namespace Polynomial

variable {R : Type*} [Semiring R]
variable [Nontrivial R]
variable (n : ℕ) (c : R) (p q : R[X])

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
def degreeLt [DegreeLe p] [DegreeEq q] :=
  DegreeLe.D p < DegreeEq.D q

-- degree of p is definitely equal to degree of q
@[simp]
def degreeEq [DegreeEq p] [DegreeEq q] :=
  DegreeEq.D p = DegreeEq.D q

-- power of leading coefficient
@[simp]
def leadingCoeffPow [LeadingCoeff p] :=
  LeadingCoeff.c p ^ n

-- product of leading coefficients
@[simp]
def leadingCoeffMul [LeadingCoeff p] [LeadingCoeff q] :=
  LeadingCoeff.c p * LeadingCoeff.c q

-- sum of leading coefficients
@[simp]
def leadingCoeffAdd [LeadingCoeff p] [LeadingCoeff q] :=
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
def degreeLe_of_degreeEq [DegreeEq p] : DegreeLe p where
  D := DegreeEq.D p
  isLe := DegreeEq.isEq.rec (WithBot.le_self (fun _ => le_of_eq rfl))

section DegreeLe

variable [DegreeLe p] [DegreeLe q]

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
    (C_0).symm.rec (degree_le_iff_coeff_zero 0 ⊥).mpr (fun _ => congrFun rfl)

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
@[simp]
instance instDegreeLePow : DegreeLe (p ^ n) where
  D := n * DegreeLe.D p
  isLe := degree_pow_le_of_le n DegreeLe.isLe

-- compute upper bound of the product of polynomials
-- given the upper bound of the polynomials
@[simp]
instance instDegreeLeMul : DegreeLe (p * q) where
  D := DegreeLe.D p + DegreeLe.D q
  isLe := degree_mul_le_of_le DegreeLe.isLe DegreeLe.isLe

-- compute upper bound of the sum of polynomials
-- given the upper bound of the polynomials
@[simp]
instance instDegreeLeAdd : DegreeLe (p + q) where
  D := max (DegreeLe.D p) (DegreeLe.D q)
  isLe := degree_add_le_of_le DegreeLe.isLe DegreeLe.isLe

end DegreeLe

section DegreeEq

variable [DegreeEq p] [DegreeEq q]

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
variable [NeZero c] in
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
variable [LeadingCoeff p] [NeZero (leadingCoeffPow n p)] in
@[simp]
instance instDegreeEqPowOfLeadingCoeff : DegreeEq (p ^ n) where
  D := DegreeEq.D p * n
  isEq :=
    have _ := LeadingCoeff.c p
    have _ := NeZero.ne (leadingCoeffPow n p)
    sorry

-- compute degree of product given leading coefficient does not become zero
variable [LeadingCoeff p] [LeadingCoeff q] [NeZero (leadingCoeffMul p q)] in
@[simp]
instance instDegreeEqMulOfLeadingCoeff : DegreeEq (p * q) where
  D := DegreeEq.D p + DegreeEq.D q
  isEq :=
    have _ := LeadingCoeff.c p
    have _ := LeadingCoeff.c q
    have _ := NeZero.ne (leadingCoeffMul p q)
    sorry

-- compute degree of sum where left side has greater degree
variable [DegreeLe q] (h : degreeLt q p) in
@[simp]
instance instDegreeEqAddLeft : DegreeEq (p + q) where
  D := DegreeEq.D p
  isEq :=
    have _ := DegreeLe.D q
    have _ := h
    sorry

-- compute degree of sum where right side has greater degree
variable [DegreeLe p] (h : degreeLt p q) in
@[simp]
instance instDegreeEqAddRight : DegreeEq (p + q) where
  D := DegreeEq.D q
  isEq :=
    have _ := DegreeLe.D p
    have _ := h
    sorry

-- compute degree of sum where sides have same degree
variable (h : degreeEq p q) in
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
variable [LeadingCoeff p] [LeadingCoeff q] [NeZero (leadingCoeffAdd p q)] in
@[simp]
instance instDegreeEqAddOfLeadingCoeff : DegreeEq (p + q) :=
  match compare (DegreeEq.D p) (DegreeEq.D q) with
  | Ordering.gt =>
    @instDegreeEqAddLeft _ _ _ _ _
      (degreeLe_of_degreeEq q)
      sorry
  | Ordering.lt =>
    @instDegreeEqAddRight _ _ _ _ _
      (degreeLe_of_degreeEq p)
      sorry
  | Ordering.eq =>
    degreeEq_add_balanced_of_leadingCoeff _ _
      sorry

end DegreeEq

section LeadingCoeff

variable [LeadingCoeff p] [LeadingCoeff q]

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
variable [NeZero (leadingCoeffPow n p)] in
@[simp]
instance instLeadingCoeffPow : LeadingCoeff (p ^ n) where
  c := LeadingCoeff.c p ^ n
  isEq :=
    have _ := NeZero.ne (leadingCoeffPow n p)
    sorry

-- compute leading coefficient of the product of polynomials
-- given the leading coefficient of the polynomials
-- given the result is nonzero
variable [NeZero (leadingCoeffMul p q)] in
@[simp]
instance instLeadingCoeffMul : LeadingCoeff (p * q) where
  c := LeadingCoeff.c p * LeadingCoeff.c q
  isEq :=
    have _ := NeZero.ne (leadingCoeffMul p q)
    sorry

-- compute leading coefficient of sum where left side has greater degree
variable [DegreeEq p] [DegreeLe q] (h : degreeLt q p) in
@[simp]
instance instLeadingCoeffAddLeft : LeadingCoeff (p + q) where
  c := LeadingCoeff.c p
  isEq :=
    LeadingCoeff.isEq.rec (leadingCoeff_add_of_degree_lt' (
      apply_degreeLt h ))

-- compute leading coefficient of sum where right side has greater degree
variable [DegreeEq q] [DegreeLe p] (h : degreeLt p q) in
@[simp]
instance instLeadingCoeffAddRight : LeadingCoeff (p + q) where
  c := LeadingCoeff.c q
  isEq :=
    LeadingCoeff.isEq.rec (leadingCoeff_add_of_degree_lt (
      apply_degreeLt h ))

-- compute leading coefficient of sum where sides have same degree
variable [NeZero (leadingCoeffAdd p q)] in
variable [DegreeEq p] [DegreeEq q] (h : degreeEq p q) in
@[simp]
def leadingCoeff_add_balanced_of_degreeEq : LeadingCoeff (p + q) where
  c := LeadingCoeff.c p + LeadingCoeff.c q
  isEq :=
    LeadingCoeff.isEq.rec (LeadingCoeff.isEq.rec (
      leadingCoeff_add_of_degree_eq (apply_degreeEq h) (
        LeadingCoeff.isEq.symm.rec (LeadingCoeff.isEq.symm.rec (
          NeZero.ne (leadingCoeffAdd p q) )) ) ))

-- compute leading coefficient of sum given both degrees
variable [NeZero (leadingCoeffAdd p q)] in
variable [DegreeEq p] [DegreeEq q] in
@[simp]
instance instLeadingCoeffAddOfDegreeEq : LeadingCoeff (p + q) :=
  match compare (DegreeEq.D p) (DegreeEq.D q) with
  | Ordering.gt =>
    @instLeadingCoeffAddLeft _ _ _ _ _ _
      (degreeLe_of_degreeEq q)
      sorry
  | Ordering.lt =>
    @instLeadingCoeffAddRight _ _ _ _ _ _
      (degreeLe_of_degreeEq p)
      sorry
  | Ordering.eq =>
    leadingCoeff_add_balanced_of_degreeEq _ _
      sorry

end LeadingCoeff

end Polynomial

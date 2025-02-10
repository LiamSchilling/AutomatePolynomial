import AutomatePolynomial.Coeff
import AutomatePolynomial.Degree
import AutomatePolynomial.Eval

namespace Polynomial

variable {R : Type*} [Semiring R]
variable (n : ℕ) (p q : R[X])

section CoeffList

variable [DegreeLe p] [Coeffs p] in
instance coeffList_of_coeffs : CoeffList p where
  C := (List.range ((DegreeLe.D p).unbot' 0).succ).map (Coeffs.C p)
  degree_lt := sorry
  coeff_eq := sorry

variable [CoeffList p] in
instance degreeLe_of_coeffList : DegreeLe p where
  D := (CoeffList.C p).length.pred
  isLe := sorry

variable [CoeffList p] in
instance coeffs_of_coeffList : Coeffs p where
  C x := ((CoeffList.C p).get? x).getD 0
  isEq := sorry

end CoeffList

section LeadingCoeff

-- retrieve leading coefficient knowing degree and all coefficients
variable [DegreeEq p] [Coeffs p] in
def leadingCoeff_of_coeffs : LeadingCoeff p :=
  ⟨ Coeffs.C p ((DegreeEq.D p).unbot' 0),
    DegreeEq.isEq.rec (Coeffs.isEq.rec rfl) ⟩

-- compute leading coefficient of sum where left side has greater degree
variable [LeadingCoeff p] in
variable [DegreeEq p] [DegreeLe q] (h : degreeLt q p) in
instance instLeadingCoeffAddLeftOfDegree : LeadingCoeff (p + q) where
  c := LeadingCoeff.c p
  isEq :=
    LeadingCoeff.isEq.rec (leadingCoeff_add_of_degree_lt' (
      apply_degreeLt h ))

-- compute leading coefficient of sum where right side has greater degree
variable [LeadingCoeff q] in
variable [DegreeLe p] [DegreeEq q] (h : degreeLt p q) in
instance instLeadingCoeffAddRightOfDegree : LeadingCoeff (p + q) where
  c := LeadingCoeff.c q
  isEq :=
    LeadingCoeff.isEq.rec (leadingCoeff_add_of_degree_lt (
      apply_degreeLt h ))

-- compute leading coefficient of sum where sides have same degree
variable [LeadingCoeff p] [LeadingCoeff q] [NeZero (leadingCoeffAdd p q)] in
variable [DegreeEq p] [DegreeEq q] (h : degreeEq p q) in
instance instLeadingCoeffAddBalancedOfDegree : LeadingCoeff (p + q) where
  c := LeadingCoeff.c p + LeadingCoeff.c q
  isEq :=
    LeadingCoeff.isEq.rec (LeadingCoeff.isEq.rec (
      leadingCoeff_add_of_degree_eq (apply_degreeEq h) (
        LeadingCoeff.isEq.symm.rec (LeadingCoeff.isEq.symm.rec (
          NeZero.ne (leadingCoeffAdd p q) )) ) ))

end LeadingCoeff

section DegreeEq

-- search for degree knowing an upper bound and all coefficients
variable [DegreeLe p] [Coeffs p] in
variable [DecidablePred (Eq 0 : R → Prop)] in
def degreeEq_of_coeffs : DegreeEq p :=
  let _ : DecidablePred (fun n => 0 = p.coeff n) := by
    rw[Coeffs.isEq]; infer_instance
  let ⟨D, h⟩ := find_degree (DegreeLe.D p) DegreeLe.isLe
  ⟨D, h⟩

-- compute degree of power given leading coefficient does not become zero
variable [DegreeEq p] in
variable [LeadingCoeff p] [NeZero (leadingCoeffPow n p)] in
instance instDegreeEqPowOfLeadingCoeff : DegreeEq (p ^ n) where
  D := DegreeEq.D p * n
  isEq :=
    have _ := LeadingCoeff.c p
    have _ := NeZero.ne (leadingCoeffPow n p)
    sorry

-- compute degree of product given leading coefficient does not become zero
variable [DegreeEq p] [DegreeEq q] in
variable [LeadingCoeff p] [LeadingCoeff q] [NeZero (leadingCoeffMul p q)] in
instance instDegreeEqMulOfLeadingCoeff : DegreeEq (p * q) where
  D := DegreeEq.D p + DegreeEq.D q
  isEq :=
    have _ := LeadingCoeff.c p
    have _ := LeadingCoeff.c q
    have _ := NeZero.ne (leadingCoeffMul p q)
    sorry

-- compute degree of sum where left side has greater degree
variable [DegreeEq p] [DegreeLe q] (h : degreeLt q p) in
instance instDegreeEqAddLeft : DegreeEq (p + q) where
  D := DegreeEq.D p
  isEq :=
    have _ := DegreeLe.D q
    have _ := h
    sorry

-- compute degree of sum where right side has greater degree
variable [DegreeLe p] [DegreeEq q] (h : degreeLt p q) in
instance instDegreeEqAddRight : DegreeEq (p + q) where
  D := DegreeEq.D q
  isEq :=
    have _ := DegreeLe.D p
    have _ := h
    sorry

-- compute degree of sum where sides have same degree
variable [DegreeEq p] [DegreeEq q] (h : degreeEq p q) in
variable [LeadingCoeff p] [LeadingCoeff q] [NeZero (leadingCoeffAdd p q)] in
instance instDegreeEqAddLeftBalancedOfLeadingCoeff : DegreeEq (p + q) where
  D := DegreeEq.D p
  isEq :=
    have _ := DegreeEq.D q
    have _ := h
    have _ := LeadingCoeff.c p
    have _ := LeadingCoeff.c q
    have _ := NeZero.ne (leadingCoeffAdd p q)
    sorry

-- compute degree of sum where sides have same degree
variable [DegreeEq p] [DegreeEq q] (h : degreeEq p q) in
variable [LeadingCoeff p] [LeadingCoeff q] [NeZero (leadingCoeffAdd p q)] in
instance instDegreeEqAddRightBalancedOfLeadingCoeff : DegreeEq (p + q) where
  D := DegreeEq.D q
  isEq :=
    have _ := DegreeEq.D p
    have _ := h
    have _ := LeadingCoeff.c p
    have _ := LeadingCoeff.c q
    have _ := NeZero.ne (leadingCoeffAdd p q)
    sorry

end DegreeEq

end Polynomial

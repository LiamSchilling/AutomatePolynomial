import AutomatePolynomial.Coeff
import AutomatePolynomial.Degree
import AutomatePolynomial.Eval

namespace Polynomial

variable {R : Type*} [Semiring R]
variable (n : ℕ) (p q : R[X])

section LeadingCoeff

def leadingCoeff_of_coeffs [DegreeEq p] [Coeffs p] : LeadingCoeff p :=
  ⟨Coeffs.C p ((DegreeEq.D p).unbot' 0), DegreeEq.isEq.rec (Coeffs.isEq.rec rfl)⟩

instance instLeadingCoeffAddLeftOfDegree [LeadingCoeff p] [DegreeEq p] [DegreeLe q] (h : degreeLt q p) : LeadingCoeff (p + q) where
  c := LeadingCoeff.c p
  isEq := LeadingCoeff.isEq.rec (leadingCoeff_add_of_degree_lt' (apply_degreeLt h))

instance instLeadingCoeffAddRightOfDegree [LeadingCoeff q] [DegreeLe p] [DegreeEq q] (h : degreeLt p q) : LeadingCoeff (p + q) where
  c := LeadingCoeff.c q
  isEq := LeadingCoeff.isEq.rec (leadingCoeff_add_of_degree_lt (apply_degreeLt h))

instance instLeadingCoeffAddBalancedOfDegree [LeadingCoeff p] [LeadingCoeff q] [DegreeEq p] [DegreeEq q] (_ : degreeEq p q) : LeadingCoeff (p + q) where
  c := LeadingCoeff.c p + LeadingCoeff.c q
  isEq := sorry

end LeadingCoeff

section DegreeEq

def degreeEq_of_coeffs [DegreeLe p] [Coeffs p] [DecidablePred (Eq 0 : R → Prop)] : DegreeEq p :=
  let _ : DecidablePred (fun n => 0 = p.coeff n) := by
    rw[Coeffs.isEq]; infer_instance
  let ⟨D, h⟩ := find_degree (DegreeLe.D p) DegreeLe.isLe
  ⟨D, h⟩

instance instDegreeEqPowOfLeadingCoeff [DegreeEq p] [LeadingCoeff p] [NeZero (leadingCoeffPow n p)] : DegreeEq (p ^ n) where
  D := DegreeEq.D p * n
  isEq := sorry

instance instDegreeEqMulOfLeadingCoeff [DegreeEq p] [DegreeEq q] [LeadingCoeff p] [LeadingCoeff q] [NeZero (leadingCoeffMul p q)] : DegreeEq (p * q) where
  D := DegreeEq.D p + DegreeEq.D q
  isEq := sorry

instance instDegreeEqAddLeft [DegreeEq p] [DegreeLe q] (_ : degreeLt q p) : DegreeEq (p + q) where
  D := DegreeEq.D p
  isEq := sorry

instance instDegreeEqAddRight [DegreeLe p] [DegreeEq q] (_ : degreeLt p q) : DegreeEq (p + q) where
  D := DegreeEq.D q
  isEq := sorry

instance instDegreeEqAddLeftBalancedOfLeadingCoeff [DegreeEq p] [DegreeEq q] (_ : degreeEq p q) [LeadingCoeff p] [LeadingCoeff q] [NeZero (leadingCoeffAdd p q)] : DegreeEq (p + q) where
  D := DegreeEq.D p
  isEq := sorry

instance instDegreeEqAddRightBalancedOfLeadingCoeff [DegreeEq p] [DegreeEq q] (_ : degreeEq p q) [LeadingCoeff p] [LeadingCoeff q] [NeZero (leadingCoeffAdd p q)] : DegreeEq (p + q) where
  D := DegreeEq.D q
  isEq := sorry

end DegreeEq

end Polynomial

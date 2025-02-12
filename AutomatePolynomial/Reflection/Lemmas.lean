import AutomatePolynomial.Reflection.Coeff
import AutomatePolynomial.Reflection.Degree
import AutomatePolynomial.Reflection.Eval

namespace Polynomial

variable {R : Type*} [Semiring R]
variable (n : ℕ) (p q : R[X])

/-
-- retrieve leading coefficient knowing degree and all coefficients
variable [DegreeEq p] [Coeffs p] in
def leadingCoeff_of_coeffs : LeadingCoeff p :=
  ⟨ Coeffs.C p ((DegreeEq.D p).unbot' 0),
    DegreeEq.isEq.rec (Coeffs.isEq.rec rfl) ⟩
-/

/-
-- search for degree knowing an upper bound and all coefficients
variable [DegreeLe p] [Coeffs p] in
variable [DecidablePred (Eq 0 : R → Prop)] in
def degreeEq_of_coeffs : DegreeEq p :=
  let _ : DecidablePred (fun n => 0 = p.coeff n) := by
    rw[Coeffs.isEq]; infer_instance
  let ⟨D, h⟩ := find_degree (DegreeLe.D p) DegreeLe.isLe
  ⟨D, h⟩
-/

end Polynomial

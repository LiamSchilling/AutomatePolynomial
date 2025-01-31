import AutomatePolynomial.Coeff
import AutomatePolynomial.Degree

namespace Polynomial

variable {R : Type*} [Semiring R]
variable [DecidablePred (Eq 0 : R → Prop)]
variable (p q : R[X])

def degreeEq_of_coeffs [DegreeLe p] [Coeffs p] : DegreeEq p :=
  let ⟨D, h⟩ := find_degree (DegreeLe.D p) DegreeLe.isLe
  ⟨D, h⟩

end Polynomial

-- PROBLEM
open Polynomial
#reduce DegreeLe.D (1 : Int[X]) -- reduces to 0 as expected
#reduce Coeffs.C (1 : Int[X]) 0 -- reduces to 1 as expected
#reduce (degreeEq_of_coeffs (1 : Int[X])).D -- does NOT reduce to 0 as expected: infers Classical.choice somewhere
example : (X + C 8 : Int[X]).degree = 1 :=
  let _ : (degreeEq_of_coeffs (0 : Int[X])).D = ⊥ := by sorry -- rfl does not resolve
  sorry

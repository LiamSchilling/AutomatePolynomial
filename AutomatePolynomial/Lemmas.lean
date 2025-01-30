import AutomatePolynomial.Coeff
import AutomatePolynomial.Degree

namespace Polynomial

variable {R : Type*} [Semiring R]
variable [DecidablePred (Eq 0 : R → Prop)]
variable (p q : R[X])

instance instDegreeEqOfCoeffs [DegreeLe p] [Coeffs p] : DegreeEq p :=
  have ⟨D, h⟩ := find_degree DegreeLe.isLe
  ⟨D, h⟩

end Polynomial

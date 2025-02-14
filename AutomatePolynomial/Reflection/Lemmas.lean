import AutomatePolynomial.Reflection.Coeff
import AutomatePolynomial.Reflection.Degree
import AutomatePolynomial.Reflection.Eval

namespace Polynomial

variable [Semiring R]

-- search for degree knowing an upper bound and all coefficients
variable (p : R[X]) [T : Coeffs p] in
variable [DecidablePred (Eq 0 : R → Prop)] in
@[simp]
def degreeEq_of_coeffs : DegreeEq p :=
  let ⟨T, h⟩ := T.to_minimal
  ⟨ T.repDegree, sorry ⟩

-- retrieve leading coefficient knowing degree and all coefficients
variable (p : R[X]) [T : Coeffs p] in
variable [DecidablePred (Eq 0 : R → Prop)] in
@[simp]
def leadingCoeff_of_coeffs : LeadingCoeff p :=
  let ⟨T, h⟩ := T.to_minimal
  ⟨ T.repLeading, sorry ⟩

end Polynomial

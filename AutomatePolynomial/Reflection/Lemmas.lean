import AutomatePolynomial.Reflection.Coeff
import AutomatePolynomial.Reflection.Degree
import AutomatePolynomial.Reflection.Eval

namespace Polynomial

variable {R : Type*} [Semiring R]
variable (n : ℕ) (p q : R[X])

-- search for degree knowing an upper bound and all coefficients
variable [T : Coeffs p] in
variable [DecidablePred (Eq 0 : R → Prop)] in
@[simp]
def degreeEq_of_coeffs : DegreeEq p :=
  let ⟨T, h⟩ := T.drop_zeros
  ⟨ T.repDegree, sorry ⟩

-- retrieve leading coefficient knowing degree and all coefficients
variable [T : Coeffs p] in
variable [DecidablePred (Eq 0 : R → Prop)] in
@[simp]
def leadingCoeff_of_coeffs : LeadingCoeff p :=
  let ⟨T, h⟩ := T.drop_zeros
  ⟨ T.repLeading, sorry ⟩

end Polynomial

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

syntax "reflect_coeff" : tactic
macro_rules
  | `(tactic| reflect_coeff) =>
    `(tactic| rw[Polynomial.Coeffs.isEq]; simp)

syntax "reflect_degree_le" : tactic
macro_rules
  | `(tactic| reflect_degree_le) =>
    `(tactic| apply Polynomial.DegreeLe.isLe)

syntax "reflect_degree_eq" : tactic
macro_rules
  | `(tactic| reflect_degree_eq) =>
    `(tactic| apply Polynomial.DegreeEq.isEq)

syntax "reflect_leading_coeff" : tactic
macro_rules
  | `(tactic| reflect_leading_coeff) =>
    `(tactic| apply Polynomial.LeadingCoeff.isEq)

syntax "reflect_eval" : tactic
macro_rules
  | `(tactic| reflect_eval) =>
    `(tactic| apply Polynomial.Eval.isEqAt)

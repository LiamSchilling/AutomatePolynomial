import AutomatePolynomial.Reflection.Polynomial.CoeffArrow
import AutomatePolynomial.Reflection.Polynomial.CoeffList
import AutomatePolynomial.Reflection.Polynomial.Degree
import AutomatePolynomial.Reflection.Polynomial.EvalArrow
import AutomatePolynomial.Reflection.Polynomial.Tactic

/-
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
    `(tactic| rw[Polynomial.Coeffs.isEqAt _]; simp)

syntax "reflect_degree_le" : tactic
macro_rules
  | `(tactic| reflect_degree_le) =>
    `(tactic| apply le_trans Polynomial.DegreeLe.isLe; try trivial)

syntax "reflect_degree_eq" : tactic
macro_rules
  | `(tactic| reflect_degree_eq) =>
    `(tactic| apply Eq.trans Polynomial.DegreeEq.isEq; try trivial)

syntax "reflect_degree_eq_trying" "<:>" tactic : tactic
macro_rules
  | `(tactic| reflect_degree_eq_trying <:> $t) =>
    `(tactic| apply Eq.trans (@Polynomial.DegreeEq.isEq _ _ _ (by infer_instance_trying <:> $t)); try trivial)
syntax "reflect_degree_eq_trying" : tactic
macro_rules
  | `(tactic| reflect_degree_eq_trying) =>
    `(tactic| reflect_degree_eq_trying <:> ( try_reg ))

syntax "reflect_leading_coeff" : tactic
macro_rules
  | `(tactic| reflect_leading_coeff) =>
    `(tactic| apply Eq.trans Polynomial.LeadingCoeff.isEq; try trivial)

syntax "reflect_leading_coeff_trying" "<:>" tactic : tactic
macro_rules
  | `(tactic| reflect_leading_coeff_trying <:> $t) =>
    `(tactic| apply Eq.trans (@Polynomial.LeadingCoeff.isEq _ _ _ (by infer_instance_trying <:> $t)); try trivial)
syntax "reflect_leading_coeff_trying" : tactic
macro_rules
  | `(tactic| reflect_leading_coeff_trying) =>
    `(tactic| reflect_leading_coeff_trying <:> ( try_reg ))

syntax "reflect_eval" : tactic
macro_rules
  | `(tactic| reflect_eval) =>
    `(tactic| apply Eq.trans (Polynomial.Eval.isEqAt _); try trivial)

syntax "reflect_expand" : tactic
macro_rules
  | `(tactic| reflect_expand) =>
    `(tactic| apply Eq.trans (Polynomial.Coeffs.expand _).property; (try simp); unfold_expand_aux; (try simp))

syntax "reflect_degree_eq_of_coeffs" : tactic
macro_rules
  | `(tactic| reflect_degree_eq_of_coeffs) =>
    `(tactic| apply Eq.trans (@Polynomial.DegreeEq.isEq _ _ _ (Polynomial.degreeEq_of_coeffs _)); try trivial)

syntax "reflect_leading_coeff_of_coeffs" : tactic
macro_rules
  | `(tactic| reflect_leading_coeff_of_coeffs) =>
    `(tactic| apply Eq.trans (@Polynomial.LeadingCoeff.isEq _ _ _ (Polynomial.leadingCoeff_of_coeffs _)); try trivial)
-/

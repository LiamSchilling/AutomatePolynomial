import AutomatePolynomial.Reflection.Polynomial.Defs
import AutomatePolynomial.Tactic.InferInstance

/-!
# *Reflection Tactics* for Polynomials

 -/

/-- Rewrites polynomials into forms with type-class instances in our reflection systems.
This is typically rewriting polynomials that are synonyms for constants as those constants.
Performing this step before the instance inference
reduces the necessary breadth of the type-class instances. -/
syntax "poly_rfl_rw" : tactic
macro_rules
| `(tactic| poly_rfl_rw) =>
  `(tactic|
    (try rw[←Polynomial.C_0]);
    (try rw[←Polynomial.C_1]); )

/-- Definitionally simplifies an expression in terms of values from inferred instances.
This step is performed after instance inference transforms the goal in terms of instances.
With a computable represenatation,
the resulting goal should be autmatically verifiable with `rfl`, `decide`, `simp`, etc. -/
syntax "poly_rfl_dsimp" : tactic
macro_rules
| `(tactic| poly_rfl_dsimp) =>
  `(tactic|
    dsimp [
      Polynomial.Rfl.DegreeLe.D,
      Polynomial.Rfl.DegreeEq.D,
      Polynomial.Rfl.LeadingCoeff.c,
      Polynomial.Rfl.Coeffs.C,
      Polynomial.Rfl.Eval.F,
      Polynomial.Rfl.FormReflection.transform,
      Polynomial.Rfl.PolyClass.inst,
      compare, compareOfLessAndEq ] )

/-- Performs type-class reflection tactic `t`
after rewriting the polynomial into a compatible form
and before definitionally simplifying the resulting instanced values in the goal. -/
syntax "poly_rfl_with" "<:>" tactic : tactic
macro_rules
| `(tactic| poly_rfl_with <:> $t) =>
  `(tactic| poly_rfl_rw; $t; poly_rfl_dsimp)

/-- A standard tactic to resolve subgoals produced during `infer_instance_trying` -/
syntax "poly_infer_try" : tactic
macro_rules
| `(tactic| poly_infer_try) =>
  `(tactic| poly_rfl_dsimp; simp)

section DegreeLe

/-- Automates goals of the form `p.degree ≤ d` -/
syntax "poly_rfl_degree_le" : tactic
macro_rules
| `(tactic| poly_rfl_degree_le) =>
  `(tactic|
    poly_rfl_with
    <:> apply le_trans (Polynomial.Rfl.DegreeLe.isLeOf
      Polynomial.Rfl.PolyClass.inst ) )

end DegreeLe

section DegreeEq

/-- Automates goals of the form `p.degree = d` -/
syntax "poly_rfl_degree_eq" : tactic
macro_rules
| `(tactic| poly_rfl_degree_eq) =>
  `(tactic|
    poly_rfl_with
    <:> apply Eq.trans (Polynomial.Rfl.DegreeEq.isEqOf
      Polynomial.Rfl.PolyClass.inst ) )

/-- Automates goals of the form `p.degree = d`
using `infer_instance_trying <:> t` to handle more complex intermediate subgoals -/
syntax "poly_rfl_degree_eq_trying" "<:>" tactic : tactic
macro_rules
| `(tactic| poly_rfl_degree_eq_trying <:> $t) =>
  `(tactic|
    poly_rfl_with
    <:> apply Eq.trans (Polynomial.Rfl.DegreeEq.isEqOf (
      Polynomial.Rfl.PolyClass.instOf (by infer_instance_trying <:> $t) )) )

/-- Automates goals of the form `p.degree = d`
by constructing a coefficient represenatation `t` with a computable degree -/
syntax "poly_rfl_degree_eq_of_coeffs" "VIA" term : tactic
macro_rules
  | `(tactic| poly_rfl_degree_eq_of_coeffs VIA $t) =>
    `(tactic|
      poly_rfl_with
      <:> apply Eq.trans (Polynomial.Rfl.DegreeEq.isEqOf (
        Polynomial.Rfl.degreeEq_use_normal (Polynomial.Rfl.PolyClass.instAs $t) )) )

end DegreeEq

section LeadingCoeff

/-- Automates goals of the form `p.leadingCoeff = c` -/
syntax "poly_rfl_leading_coeff" : tactic
macro_rules
| `(tactic| poly_rfl_leading_coeff) =>
  `(tactic|
    poly_rfl_with
    <:> apply Eq.trans (Polynomial.Rfl.LeadingCoeff.isEqOf
      Polynomial.Rfl.PolyClass.inst ) )

/-- Automates goals of the form `p.leadingCoeff = c`
using `infer_instance_trying <:> t` to handle more complex intermediate subgoals -/
syntax "poly_rfl_leading_coeff_trying" "<:>" tactic : tactic
macro_rules
| `(tactic| poly_rfl_leading_coeff_trying <:> $t) =>
  `(tactic|
    poly_rfl_with
    <:> apply Eq.trans (Polynomial.Rfl.LeadingCoeff.isEqOf (
      Polynomial.Rfl.PolyClass.instOf (by infer_instance_trying <:> $t) )) )

/-- Automates goals of the form `p.leadingCoeff = c`
by constructing a coefficient represenatation `t` with a computable leading coefficient -/
syntax "poly_rfl_leading_coeff_of_coeffs" "VIA" term : tactic
macro_rules
| `(tactic| poly_rfl_leading_coeff_of_coeffs VIA $t) =>
  `(tactic|
    poly_rfl_with
    <:> apply Eq.trans (Polynomial.Rfl.LeadingCoeff.isEqOf (
      Polynomial.Rfl.leadingCoeff_use_normal (Polynomial.Rfl.PolyClass.instAs $t) )) )

end LeadingCoeff

section Coeffs

/-- Automates goals of the form `p.coeff n = c`
using coefficient representation `t` -/
syntax "poly_rfl_coeff" "VIA" term : tactic
macro_rules
| `(tactic| poly_rfl_coeff VIA $t) =>
  `(tactic|
    poly_rfl_with
    <:> apply Eq.trans (Polynomial.Rfl.Coeffs.isEqAtOf (
      Polynomial.Rfl.PolyClass.instAs $t ) _) )

end Coeffs

section Eval

/-- Automates goals of the form `p.eval x = y`
using evaluation representation `t` -/
syntax "poly_rfl_eval" "VIA" term : tactic
macro_rules
| `(tactic| poly_rfl_eval VIA $t) =>
  `(tactic|
    poly_rfl_with
    <:> apply Eq.trans (Polynomial.Rfl.Eval.isEqAtOf (
      Polynomial.Rfl.PolyClass.instAs $t ) _) )

end Eval

section Transform

/-- Automates goals of the form `p = q`
by rewriting the `p` into a normal form determined by coefficient representation `t` -/
syntax "poly_rfl_expand" "VIA" term : tactic
macro_rules
| `(tactic| poly_rfl_expand VIA $t) =>
  `(tactic|
    poly_rfl_with
    <:> apply Eq.trans (Polynomial.Rfl.FormReflection.transform (
      Polynomial.Rfl.PolyClass.instAs $t )).property )

end Transform

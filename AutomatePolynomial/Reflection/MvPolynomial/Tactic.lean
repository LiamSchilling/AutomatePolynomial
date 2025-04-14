import AutomatePolynomial.Reflection.MvPolynomial.Defs
import AutomatePolynomial.Tactic.InferInstance

/-!
# *Reflection Tactics* for Multivariate Polynomials

 -/

/-- Rewrites polynomials into forms with type-class instances in our reflection systems.
This is typically rewriting polynomials that are synonyms for constants as those constants.
Performing this step before the instance inference
reduces the necessary breadth of the type-class instances. -/
syntax "mv_poly_rfl_rw" : tactic
macro_rules
| `(tactic| mv_poly_rfl_rw) =>
  `(tactic|
    (try rw[←MvPolynomial.C_0]);
    (try rw[←MvPolynomial.C_1]) )

/-- Definitionally simplifies an expression in terms of values from inferred instances.
This step is performed after instance inference transforms the goal in terms of instances.
With a computable represenatation,
the resulting goal should be autmatically verifiable with `rfl`, `decide`, `simp`, etc. -/
syntax "mv_poly_rfl_dsimp" : tactic
macro_rules
| `(tactic| mv_poly_rfl_dsimp) =>
  `(tactic|
    dsimp [
      MvPolynomial.Rfl.MvVarsLe.V,
      MvPolynomial.Rfl.MvWeightedTotalDegreeLe.D,
      MvPolynomial.Rfl.MvCoeffs.C,
      MvPolynomial.Rfl.MvEval.F,
      MvPolynomial.Rfl.MvFormReflection.transform,
      MvPolynomial.Rfl.MvPolyClass.inst,
      compare, compareOfLessAndEq ] )

/-- Performs type-class reflection tactic `t`
after rewriting the polynomial into a compatible form
and before definitionally simplifying the resulting instanced values in the goal. -/
syntax "mv_poly_rfl_with" "<:>" tactic : tactic
macro_rules
| `(tactic| mv_poly_rfl_with <:> $t) =>
  `(tactic| mv_poly_rfl_rw; $t; mv_poly_rfl_dsimp)

/-- A standard tactic to resolve subgoals produced during `infer_instance_trying` -/
syntax "mv_poly_infer_try" : tactic
macro_rules
| `(tactic| mv_poly_infer_try) =>
  `(tactic| mv_poly_rfl_dsimp; simp)

section MvVarsLe

/-- Automates goals of the form `p.vars ⊆ V`
using variable representation `t` -/
syntax "mv_poly_rfl_vars_le" "VIA" term : tactic
macro_rules
| `(tactic| mv_poly_rfl_vars_le VIA $t) =>
  `(tactic|
    mv_poly_rfl_with
    <:> apply subset_trans (MvPolynomial.Rfl.MvVarsLe.isLeOf (
      MvPolynomial.Rfl.MvPolyClass.instAs $t )) )

end MvVarsLe

section MvWeightedTotalDegreeLe

/-- Automates goals of the form `p.weightedTotalDegree w ≤ D` -/
syntax "mv_poly_rfl_weighted_total_degree_le" : tactic
macro_rules
| `(tactic| mv_poly_rfl_weighted_total_degree_le) =>
  `(tactic|
    mv_poly_rfl_with
    <:> apply le_trans (MvPolynomial.Rfl.MvWeightedTotalDegreeLe.isLeOf
      MvPolynomial.Rfl.MvPolyClass.inst ) )

end MvWeightedTotalDegreeLe

section MvCoeffs

/-- Automates goals of the form `p.coeff m = c`
using coefficient representation `t` -/
syntax "mv_poly_rfl_coeff" "VIA" term : tactic
macro_rules
| `(tactic| mv_poly_rfl_coeff VIA $t) =>
  `(tactic|
    mv_poly_rfl_with
    <:> apply Eq.trans (MvPolynomial.Rfl.MvCoeffs.isEqAtOf (
      MvPolynomial.Rfl.MvPolyClass.instAs $t ) _) )

end MvCoeffs

section MvEval

/-- Automates goals of the form `p.eval x = y`
using evaluation representation `t` -/
syntax "mv_poly_rfl_eval" "VIA" term : tactic
macro_rules
| `(tactic| mv_poly_rfl_eval VIA $t) =>
  `(tactic|
    mv_poly_rfl_with
    <:> apply Eq.trans (MvPolynomial.Rfl.MvEval.isEqAtOf (
      MvPolynomial.Rfl.MvPolyClass.instAs $t ) _) )

end MvEval

section Transform

/-- Automates goals of the form `p = q`
by rewriting the `p` into a normal form determined by coefficient representation `t` -/
syntax "mv_poly_rfl_expand" "VIA" term : tactic
macro_rules
| `(tactic| mv_poly_rfl_expand VIA $t) =>
  `(tactic|
    mv_poly_rfl_with
    <:> apply Eq.trans (MvPolynomial.Rfl.MvFormReflection.transform (
      MvPolynomial.Rfl.MvPolyClass.instAs $t )).property )

end Transform

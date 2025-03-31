import AutomatePolynomial.Reflection.MvPolynomial.Defs
import AutomatePolynomial.Tactic.InferInstance

section System

syntax "mv_poly_rw_C" : tactic
macro_rules
  | `(tactic| mv_poly_rw_C) =>
    `(tactic|
      (try rw[←MvPolynomial.C_0]);
      (try rw[←MvPolynomial.C_1]) )

syntax "mv_poly_dsimp_inst" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| mv_poly_dsimp_inst [$ids,*]) =>
    `(tactic|
      dsimp [
        MvPolynomial.MvDegreeLe.D,
        MvPolynomial.MvVarsLe.V,
        MvPolynomial.MvCoeffs.C,
        MvPolynomial.MvEval.F,
        MvPolynomial.MvPolynomialFormReflection.transform,
        MvPolynomial.MvPolyClass.inst,
        $ids,* ] )

syntax
    "mv_poly_reflect_with" "[" Lean.Parser.Tactic.simpLemma,* "]"
    "<:>" tactic :
  tactic
macro_rules
  | `(tactic| mv_poly_reflect_with [$ids,*] <:> $t) =>
    `(tactic| mv_poly_rw_C; $t; mv_poly_dsimp_inst [$ids,*])

syntax
    "mv_poly_reflect_with_cmp" "[" Lean.Parser.Tactic.simpLemma,* "]"
    "<:>" tactic :
  tactic
macro_rules
  | `(tactic| mv_poly_reflect_with_cmp [$ids,*] <:> $t) =>
    `(tactic| mv_poly_reflect_with [compare, compareOfLessAndEq, $ids,*] <:> $t)

-- intended for combination with infer_instance_trying
-- in the polynomial synthesis problem
syntax "mv_poly_try" : tactic
macro_rules
  | `(tactic| mv_poly_try) =>
    `(tactic| mv_poly_dsimp_inst []; simp; try infer_instance )

end System

section MvDegreeLe

section MvDegreeLe

syntax "mv_poly_reflect_degree_le" : tactic
macro_rules
  | `(tactic| mv_poly_reflect_degree_le) =>
    `(tactic|
      mv_poly_reflect_with []
      <:> apply le_trans (MvPolynomial.MvDegreeLe.isLeOf
        MvPolynomial.MvPolyClass.inst ) )

syntax "mv_poly_reflect_degree_le_trying" "<:>" tactic : tactic
macro_rules
  | `(tactic| mv_poly_reflect_degree_le_trying <:> $t) =>
    `(tactic|
      mv_poly_reflect_with []
      <:> apply le_trans (MvPolynomial.MvDegreeLe.isLeOf (
        MvPolynomial.MvPolyClass.instOf (by infer_instance_trying <:> $t) )) )

end MvDegreeLe

section MvVarsLe

syntax "mv_poly_reflect_vars_le" "VIA" term : tactic
macro_rules
  | `(tactic| mv_poly_reflect_vars_le VIA $t) =>
    `(tactic|
      mv_poly_reflect_with_cmp []
      <:> apply subset_trans (MvPolynomial.MvVarsLe.isLeOf (
        MvPolynomial.MvPolyClass.instAs $t )) )

end MvVarsLe

section MvCoeffsAndEval

syntax "mv_poly_reflect_coeff" "VIA" term : tactic
macro_rules
  | `(tactic| mv_poly_reflect_coeff VIA $t) =>
    `(tactic|
      mv_poly_reflect_with []
      <:> apply Eq.trans (MvPolynomial.MvCoeffs.isEqAtOf (
        MvPolynomial.MvPolyClass.instAs $t ) _) )

syntax "mv_poly_reflect_eval" "VIA" term : tactic
macro_rules
  | `(tactic| mv_poly_reflect_eval VIA $t) =>
    `(tactic|
      mv_poly_reflect_with []
      <:> apply Eq.trans (MvPolynomial.MvEval.isEqAtOf (
        MvPolynomial.MvPolyClass.instAs $t ) _) )

syntax "mv_poly_reflect_expand" "VIA" term : tactic
macro_rules
  | `(tactic| mv_poly_reflect_expand VIA $t) =>
    `(tactic|
      mv_poly_reflect_with_cmp []
      <:> apply Eq.trans (MvPolynomial.MvPolynomialFormReflection.transform (
        MvPolynomial.MvPolyClass.instAs $t )).property )

end MvCoeffsAndEval

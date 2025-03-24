import AutomatePolynomial.Reflection.Polynomial.Defs
import AutomatePolynomial.Tactic.InferInstance

section System

syntax "poly_rw_C" : tactic
macro_rules
  | `(tactic| poly_rw_C) =>
    `(tactic|
      (try rw[←Polynomial.C_0]);
      (try rw[←Polynomial.C_1]) )

syntax "poly_dsimp_inst" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| poly_dsimp_inst [$ids,*]) =>
    `(tactic|
      dsimp [
        Polynomial.DegreeLe.D,
        Polynomial.DegreeEq.D,
        Polynomial.LeadingCoeff.c,
        Polynomial.Coeffs.C,
        Polynomial.Eval.F,
        Polynomial.PolynomialFormReflection.transform,
        Polynomial.PolyClass.inst,
        $ids,* ] )

syntax
    "poly_reflect_with" "[" Lean.Parser.Tactic.simpLemma,* "]"
    "<:>" tactic :
  tactic
macro_rules
  | `(tactic| poly_reflect_with [$ids,*] <:> $t) =>
    `(tactic| poly_rw_C; $t; poly_dsimp_inst [$ids,*])

syntax
    "poly_reflect_with_sns" "[" Lean.Parser.Tactic.simpLemma,* "]"
    "<:>" tactic :
  tactic
macro_rules
  | `(tactic| poly_reflect_with_sns [$ids,*] <:> $t) =>
    `(tactic| poly_reflect_with [compare, compareOfLessAndEq, $ids,*] <:> $t)

-- intended for combination with infer_instance_trying
-- in the polynomial synthesis problem
syntax "poly_try" : tactic
macro_rules
  | `(tactic| poly_try) =>
    `(tactic| poly_dsimp_inst [compare, compareOfLessAndEq]; simp; try infer_instance )

end System

section DegreeLe

syntax "poly_reflect_degree_le" : tactic
macro_rules
  | `(tactic| poly_reflect_degree_le) =>
    `(tactic|
      poly_reflect_with []
      <:> apply le_trans (Polynomial.DegreeLe.isLeOf
        Polynomial.PolyClass.inst ) )

end DegreeLe

section DegreeEq

syntax "poly_reflect_degree_eq" : tactic
macro_rules
  | `(tactic| poly_reflect_degree_eq) =>
    `(tactic|
      poly_reflect_with_sns []
      <:> apply Eq.trans (Polynomial.DegreeEq.isEqOf
        Polynomial.PolyClass.inst ) )

syntax "poly_reflect_degree_eq_trying" "<:>" tactic : tactic
macro_rules
  | `(tactic| poly_reflect_degree_eq_trying <:> $t) =>
    `(tactic|
      poly_reflect_with_sns []
      <:> apply Eq.trans (Polynomial.DegreeEq.isEqOf (
        Polynomial.PolyClass.instOf (by infer_instance_trying <:> $t) )) )

syntax "poly_reflect_degree_eq_of_coeffs" "VIA" term : tactic
macro_rules
  | `(tactic| poly_reflect_degree_eq_of_coeffs VIA $t) =>
    `(tactic|
      poly_reflect_with_sns []
      <:> apply Eq.trans (Polynomial.DegreeEq.isEqOf (
        Polynomial.degreeEq_of_normal (Polynomial.PolyClass.instAs $t) )) )

end DegreeEq

section LeadingCoeff

syntax "poly_reflect_leading_coeff" : tactic
macro_rules
  | `(tactic| poly_reflect_leading_coeff) =>
    `(tactic|
      poly_reflect_with_sns []
      <:> apply Eq.trans (Polynomial.LeadingCoeff.isEqOf
        Polynomial.PolyClass.inst ) )

syntax "poly_reflect_leading_coeff_trying" "<:>" tactic : tactic
macro_rules
  | `(tactic| poly_reflect_leading_coeff_trying <:> $t) =>
    `(tactic|
      poly_reflect_with_sns []
      <:> apply Eq.trans (Polynomial.LeadingCoeff.isEqOf (
        Polynomial.PolyClass.instOf (by infer_instance_trying <:> $t) )) )

syntax "poly_reflect_leading_coeff_of_coeffs" "VIA" term : tactic
macro_rules
  | `(tactic| poly_reflect_leading_coeff_of_coeffs VIA $t) =>
    `(tactic|
      poly_reflect_with_sns []
      <:> apply Eq.trans (Polynomial.LeadingCoeff.isEqOf (
        Polynomial.leadingCoeff_of_normal (Polynomial.PolyClass.instAs $t) )) )

end LeadingCoeff

section CoeffsAndEval

syntax "poly_reflect_coeff" "VIA" term : tactic
macro_rules
  | `(tactic| poly_reflect_coeff VIA $t) =>
    `(tactic|
      poly_reflect_with []
      <:> apply Eq.trans (Polynomial.Coeffs.isEqAtOf (
        Polynomial.PolyClass.instAs $t ) _) )

syntax "poly_reflect_eval" "VIA" term : tactic
macro_rules
  | `(tactic| poly_reflect_eval VIA $t) =>
    `(tactic|
      poly_reflect_with []
      <:> apply Eq.trans (Polynomial.Eval.isEqAtOf (
        Polynomial.PolyClass.instAs $t ) _) )

syntax "poly_reflect_expand" "VIA" term : tactic
macro_rules
  | `(tactic| poly_reflect_expand VIA $t) =>
    `(tactic|
      poly_reflect_with []
      <:> apply Eq.trans (Polynomial.PolynomialFormReflection.transform (
        Polynomial.PolyClass.instAs $t )).property )

end CoeffsAndEval

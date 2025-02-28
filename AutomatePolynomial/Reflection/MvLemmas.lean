import AutomatePolynomial.Reflection.MvCoeff
import AutomatePolynomial.Reflection.MvDegree
import AutomatePolynomial.Util.Tactics

syntax "reflect_coeff" : tactic
macro_rules
  | `(tactic| reflect_coeff) =>
    `(tactic| rw[MvPolynomial.MvCoeffs.isEqAt _]; simp [compare, compareOfLessAndEq, cast_eq_iff_heq, List.heq_of])

syntax "reflect_mv_degree_le" : tactic
macro_rules
  | `(tactic| reflect_mv_degree_le) =>
    `(tactic| apply le_trans MvPolynomial.MvDegreeLe.isLe; try trivial)

syntax "reflect_mv_degree_le_trying" "<:>" tactic : tactic
macro_rules
  | `(tactic| reflect_mv_degree_le_trying <:> $t) =>
    `(tactic| apply le_trans (@MvPolynomial.MvDegreeLe.isLe _ _ _ _ _ (by infer_instance_trying <:> $t)); try trivial)
syntax "reflect_mv_degree_le_trying" : tactic
macro_rules
  | `(tactic| reflect_mv_degree_le_trying) =>
    `(tactic| reflect_mv_degree_le_trying <:> ( try_reg ))

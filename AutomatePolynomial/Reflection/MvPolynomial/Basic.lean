import AutomatePolynomial.Reflection.MvPolynomial.Coeff
import AutomatePolynomial.Reflection.MvPolynomial.Degree
import AutomatePolynomial.Tactic.InferInstance

/-
syntax "reflect_mv_coeff" : tactic
macro_rules
  | `(tactic| reflect_mv_coeff) =>
    `(tactic| rw[MvPolynomial.MvCoeffs.isEqAt _]; simp [Fin.foldrM, Fin.foldrM.loop])

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
-/

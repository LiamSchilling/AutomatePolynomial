import Mathlib.Algebra.Polynomial.Degree.Lemmas

namespace Polynomial

variable {R : Type*} [Semiring R]
variable {p : R[X]}

-- get degree of polynomial by searching coefficients
variable [DecidablePred (fun n => 0 = coeff p n)] in
def find_degree (D : WithBot ℕ) (h1 : degree p ≤ D) :
    { D' // degree p = D' } :=
  match D with
  | ⊥ =>
    ⟨⊥, le_bot_iff.mp h1⟩
  | some D =>
  match inferInstanceAs (Decidable (0 = coeff p D)) with
  | isFalse h2 =>
    ⟨some D, degree_eq_of_le_of_coeff_ne_zero h1 (fun hn => h2 hn.symm)⟩
  | isTrue h2 =>
  match D with
  | 0 =>
    have h5 : p.degree ≤ ⊥ := by
      apply (degree_le_iff_coeff_zero _ _).mpr
      intro N h3
      match N with
      | 0 => exact h2.symm
      | N + 1 =>
        rw[(degree_le_iff_coeff_zero _ _).mp h1]
        exact compare_gt_iff_gt.mp rfl
    find_degree ⊥ h5
  | D + 1 =>
    have h5 : p.degree ≤ some D := by
      apply (degree_le_iff_coeff_zero _ _).mpr
      intro N h3
      match inferInstanceAs (Decidable (some D.succ = N)) with
      | isFalse h4 =>
        rw[(degree_le_iff_coeff_zero _ _).mp h1]
        apply WithBot.coe_lt_coe.mpr
        apply lt_of_le_of_ne
        . exact WithBot.coe_lt_coe.mp h3
        . intro hn; rw[Nat.succ_eq_add_one, hn] at h4; contradiction
      | isTrue h4 =>
        rw[←WithBot.coe_inj.mp h4]
        exact h2.symm
    find_degree (some D) h5
termination_by match D with | ⊥ => 0 | some D => D.succ

@[simp]
def Coeffs.addBalancedAux (cs1 cs2 : List R) : List R :=
  (List.zip cs1 cs2).map (fun (cp, cq) => cp + cq)

@[simp]
def Coeffs.addAux (cs1 cs2 : List R) : List R :=
  addBalancedAux
    (List.replicate (max cs1.length cs2.length - cs1.length) 0 ++ cs1)
    (List.replicate (max cs1.length cs2.length - cs2.length) 0 ++ cs2)

@[simp]
def Coeffs.mulConstAux (c : R) (cs : List R) : List R :=
  cs.map (fun c' => c * c')

@[simp]
def Coeffs.mulXPowAux (n : ℕ) (cs : List R) : List R :=
  cs ++ List.replicate n 0

@[simp]
def Coeffs.mulAux (cs1 cs2 : List R) : List R :=
  match cs1 with
  | [] => List.replicate cs2.length.pred 0
  | c :: cs1 => addAux (mulAux cs1 cs2) (mulConstAux c (mulXPowAux cs1.length cs2))

@[simp]
def Coeffs.powAux (n : ℕ) (cs : List R) : List R :=
  match n with
  | 0 => [1]
  | n + 1 => mulAux (powAux n cs) cs

-- given coefficients [cn, ... c1, c0]
-- computes abstract polynomial (c0 + c1*x + ... cn*x^n)
noncomputable def Coeffs.expandAux (cs : List R) (n : Nat) (h : cs.length = n) : R[X] :=
  match cs with
  | [] => 0
  | c :: cs => expandAux cs n.pred (Nat.pred_eq_of_eq_succ h.symm).symm + C c * X ^ n.pred

end Polynomial

-- fully unfold expand call
syntax "unfold_expand_aux" : tactic
macro_rules
  | `(tactic| unfold_expand_aux) =>
    `(tactic| repeat unfold Polynomial.Coeffs.expandAux)

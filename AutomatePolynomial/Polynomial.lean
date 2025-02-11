import AutomatePolynomial.Algebra
import Mathlib.Algebra.Polynomial.Degree.Lemmas

namespace Polynomial

variable {R : Type*} [Semiring R]
variable {n m : ℕ} {p q : R[X]}

-- degree of polynomial sums is maximum of polynomial degrees
variable [NoAdditiveInverses R] in
lemma degree_add_eq_of_eq (hp : degree p = n) (hq : degree q = m) :
    degree (p + q) = max n m := by
  apply degree_eq_of_le_of_coeff_ne_zero
  . apply (degree_le_iff_coeff_zero _ _).mpr
    intro N h
    rw[coeff_add]
    have ⟨hn, hm⟩ := Nat.max_lt.mp (WithBot.coe_lt_coe.mp h)
    rw[coeff_eq_zero_of_degree_lt (by rw[hp]; exact WithBot.coe_lt_coe.mpr hn)]
    rw[coeff_eq_zero_of_degree_lt (by rw[hq]; exact WithBot.coe_lt_coe.mpr hm)]
    simp
  . rw[coeff_add]
    cases max_choice n m <;> (rename_i h; rw[h]; intro h)
    . absurd coeff_ne_zero_of_eq_degree hp
      exact (NoAdditiveInverses.eq_zero_and_eq_zero_of_add_eq_zero h).left
    . absurd coeff_ne_zero_of_eq_degree hq
      exact (NoAdditiveInverses.eq_zero_and_eq_zero_of_add_eq_zero h).right

-- degree of polynomial sums is maximum of polynomial degrees
variable [NoAdditiveInverses R] in
lemma degree_add :
    degree (p + q) = max (degree p) (degree q) :=
  match hp : degree p with
  | ⊥ => by simp [degree_eq_bot.mp hp]
  | some n =>
  match hq : degree q with
  | ⊥ => by simp [degree_eq_bot.mp hq, hp]
  | some m => degree_add_eq_of_eq hp hq

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

partial def coeff_list_mul_rec (ret : Bool) (C1L C1R C2L C2R accL accR : List R) : List R :=
  match ret, C1L, C1R, C2L, C2R, accL, accR with
  | false, c1 :: C1L,       [] ,       C2L,       C2R,      accL,      accR => coeff_list_mul_rec false C1L [c1] C2L C2R accL accR
  | false,       C1L, c1 :: C1R, c2 :: C2L,       C2R,      []  ,      accR => coeff_list_mul_rec false C1L (c1 :: C1R) C2L (c2 :: C2R) accL ((c1 * c2) :: accR)
  | false,       C1L, c1 :: C1R, c2 :: C2L,       C2R, c :: accL,      accR => coeff_list_mul_rec false C1L (c1 :: C1R) C2L (c2 :: C2R) accL ((c + c1 * c2) :: accR)
  | false, c1 :: C1L,       C1R,       C2L,       C2R,      accL,      accR => coeff_list_mul_rec true C1L (c1 :: C1R) C2L C2R accL accR
  | true ,       C1L,       C1R,       C2L, c2 :: C2R,      accL, c :: accR => coeff_list_mul_rec true C1L C1R (c2 :: C2L) C2R (c :: accL) accR
  | true ,       C1L,       C1R,       C2L,       [] , c :: accL,      accR => coeff_list_mul_rec false C1L C1R C2L [] accL (c :: accR)
  | _    ,       _  ,       _  ,       _  ,       _  ,      accL,      accR => accR.reverse ++ accL

def coeff_list_mul (C1 C2 : List R) : List R :=
  coeff_list_mul_rec false C1 [] C2 [] [] []

def coeff_list_pow_rec (n : Nat) (C acc : List R) : List R :=
  match n with
  | 0 => acc
  | n + 1 => coeff_list_pow_rec n C (coeff_list_mul acc C)

def coeff_list_pow (n : Nat) (C : List R) : List R :=
  coeff_list_pow_rec n C [1]

-- given coefficients [cn, ... c1, c0]
-- computes abstract polynomial (c0 + c1*x + ... cn*x^n)
noncomputable def expand_rec (cs : List R) (n : Nat) (h : cs.length = n) : R[X] :=
  match cs with
  | [] => 0
  | c :: cs => expand_rec cs n.pred (Nat.pred_eq_of_eq_succ h.symm).symm + C c * X ^ n

-- given coefficients [c0, c1, ... cn]
-- computes abstract polynomial (c0 + c1*x + ... cn*x^n)
noncomputable def expand (cs : List R) : R[X] :=
  expand_rec cs.reverse cs.length cs.length_reverse

end Polynomial

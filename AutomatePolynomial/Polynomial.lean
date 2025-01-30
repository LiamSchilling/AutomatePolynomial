import AutomatePolynomial.Algebra
import Mathlib.Algebra.Polynomial.Degree.Lemmas

namespace Polynomial

variable {R : Type*} [Semiring R]
variable {n m : ℕ} {p q : R[X]}
variable {D : WithBot ℕ}

-- degree of polynomial sums is maximum of polynomial degrees
variable [NoAdditiveInverses R] in
lemma degree_add_eq_of_eq (hp : degree p = n) (hq : degree q = m) :
    degree (p + q) = max n m := by
  apply degree_eq_of_le_of_coeff_ne_zero
  . apply (Polynomial.degree_le_iff_coeff_zero _ _).mpr
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
def find_degree (h : degree p ≤ D) : { D' // degree p = D' } :=
  have _ : DecidablePred (fun n => 0 = coeff p n) := inferInstance
  sorry

end Polynomial

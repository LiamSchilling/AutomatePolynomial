import AutomatePolynomial.Hyperlist.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# *Representation*: Coefficient Lists

We use `List` as a dense representation of polynomial coefficients.

 -/

namespace Polynomial.CoeffList

section Semiring

variable [Semiring R]

/-- Representation invariant for coefficient lists -/
def reps (p : R[X]) (C : List R) :=
  ∀ n, p.coeff n = C[n]?.getD 0

/-- Coefficient list operation corresponding to polynomial addition -/
@[simp]
def add (L1 L2 : List R) :=
  List.zipWithPad (. + .) 0 0 L1 L2

theorem length_add {L1 L2 : List R} :
    (add L1 L2).length = max L1.length L2.length := by
  exact List.length_zipWithPad

theorem getD_add {n : ℕ} {L1 L2 : List R} :
    (add L1 L2)[n]?.getD 0 = L1[n]?.getD 0 + L2[n]?.getD 0 := by
  nth_rw 1 [←zero_add 0]; exact List.getD_zipWithPad

theorem reps_add  {L1 L2 : List R}
    (h1 : reps p L1) (h2 : reps q L2) :
    reps (p + q) (add L1 L2) := by
  intro; rw[getD_add, ←h1, ←h2]; simp

/-- Coefficient list operation corresponding to polynomial multiplication by a constant -/
@[simp]
def mulC (c : R) (L : List R) :=
  List.map (c * .) L

theorem length_mulC {L : List R} :
    (mulC c L).length = L.length := by
  simp

theorem getD_mulC {n : ℕ} {L : List R} :
    (mulC c L)[n]?.getD 0 = c * L[n]?.getD 0 := by
  simp
  cases Nat.decLt n L.length <;> (rename_i h; simp at h)
  . rw[List.getElem?_eq_none]; simp; assumption
  . rw[(List.getElem?_eq_some_getElem_iff h).mpr trivial]; simp

theorem rep_mulC {L : List R}
    (h : reps p L) :
    reps (C c * p) (mulC c L) := by
  intro; rw[getD_mulC, ←h]; simp

/-- Coefficient list operation corresponding to polynomial multiplication by `X` -/
@[simp]
def mulX (L : List R) :=
  0 :: L

theorem length_mulX {L : List R} :
    (mulX L).length = L.length + 1 := by
  simp

theorem getD_mulX {n : ℕ} {L : List R} :
    (mulX L)[n]?.getD 0 =
    match n with
    | 0 => 0
    | n' + 1 => L[n']?.getD 0 := by
  cases n <;> simp

theorem reps_mulX {L : List R}
    (h : reps p L) :
    reps (X * p) (mulX L) := by
  intro n; rw[getD_mulX]; cases n <;> simp; rw[←h]

end Semiring

section CommSemiring

variable [CommSemiring R]

/-- Coefficient list operation corresponding to polynomial multiplication by `X ^ n` -/
@[simp]
def mulXPow (n : ℕ) (L : List R) :=
  match n with
  | 0 => L
  | n' + 1 => mulX (mulXPow n' L)

theorem length_mulXPowAux {L : List R} :
    (mulXPow n L).length = L.length + n := by
  cases n <;> simp; rw[length_mulXPowAux, add_assoc]

theorem reps_mulXPow {L : List R}
    (h : reps p L) :
    reps (X ^ n * p) (mulXPow n L) := by
  cases n <;> simp; assumption
  intro n; cases n <;> simp
  rw[←reps_mulXPow h, pow_succ]; nth_rw 2 [mul_comm]; rw[mul_assoc]; simp

/-- Coefficient list operation corresponding to polynomial multiplication -/
@[simp]
def mul (L1 L2 : List R) :=
  match L1 with
  | [] => List.replicate L2.length.pred 0
  | c :: L1' => add (mulC c L2) (mulX (mul L1' L2))

theorem length_mul {L1 L2 : List R} :
    (mul L1 L2).length = L1.length + L2.length.pred := by
  cases L1; simp
  unfold mul; rw[length_add]; simp; rw[length_mul]
  rw[max_eq_right, add_right_comm]; rfl
  apply Nat.le_add_of_sub_le; apply le_add_left; rfl

theorem reps_mul {L1 L2 : List R}
    (h1 : reps p L1) (h2 : reps q L2) :
    reps (p * q) (mul L1 L2) := by
  cases L1 <;> unfold mul
  . intro n
    rw[leadingCoeff_eq_zero.mp (h1 p.natDegree)]
    cases Nat.decLt n L2.length.pred <;> (rename_i h; simp at h)
    . rw[List.getElem?_eq_none]; simp; simpa
    . rw[(List.getElem?_eq_some_getElem_iff (by simpa)).mpr trivial]; simp
  . rename_i L1'; sorry

/-- Coefficient list operation corresponding to polynomial power -/
@[simp]
def power (n : ℕ) (L : List R) :=
  match n with
  | 0 => [1]
  | n' + 1 => mul (power n' L) L

theorem length_power {L : List R} :
    (power n L).length = n * L.length.pred + 1 := by
  cases n <;> simp
  rw[length_mul, length_power]
  rw[add_comm, ←add_assoc]; nth_rw 2 [add_comm]; rw[mul_comm, ←Nat.mul_succ, mul_comm]; rfl

theorem reps_power {L : List R}
    (h : reps p L) :
    reps (p ^ n) (power n L) := by
  cases n <;> simp
  . intro n; rw[coeff_one]; cases n <;> simp
  . rw[pow_succ]; sorry

end CommSemiring

section Semiring

variable [Semiring R]

/-- TODO: CLEAN & DOCSTRING

given coefficients [c0, c1, ... cn]
computes abstract polynomial (cn*x^n + ... c1*x + c0) -/
noncomputable def expandAux (cs : List R) (n : ℕ) :=
  match cs with
  | [] => 0
  | c :: cs => expandAux cs n.succ + C c * X ^ n

lemma expandAux_coeff
    {cs : List R} {N : ℕ} :
    (expandAux cs N).coeff n =
    if n < N then 0 else cs[n - N]?.getD 0 := by
  cases cs
  . unfold expandAux
    cases inferInstanceAs (Decidable (n < N)) <;> rename_i h
    . rw[if_neg h]; rfl
    . rw[if_pos h]; rfl
  . unfold expandAux; simp; rw[expandAux_coeff]
    cases inferInstanceAs (Decidable (n < N)) <;>
    cases inferInstanceAs (Decidable (n < N + 1)) <;>
    rename_i h1 h2
    . rw[if_neg h1, if_neg h2]
      simp at h2
      rw[if_neg, Nat.sub_succ, ←Nat.succ_pred (Nat.sub_ne_zero_of_lt h2)]; simp
      apply Nat.ne_of_lt'; assumption
    . rw[if_neg h1, if_pos h2]
      rw[show n = N by apply Nat.eq_of_lt_succ_of_not_lt <;> assumption]; simp
    . absurd h2; apply Nat.lt_add_right; assumption
    . rw[if_pos h1, if_pos h2]
      rw[if_neg]; simp
      apply ne_of_lt; assumption

lemma expandAux_eq
    {p : R[X]} {cs : List R} {N : ℕ} :
    (∀ n, n < N → p.coeff n = 0) →
    (∀ n, p.coeff (N + n) = cs[n]?.getD 0) →
    p = expandAux cs N := by
  intro h1 h2; apply ext; intro n
  rw[expandAux_coeff]
  cases inferInstanceAs (Decidable (n < N)) <;> rename_i h3
  . rw[if_neg h3, ←h2]; simp at h3
    apply congrArg; symm; apply Nat.add_sub_of_le; assumption
  . rw[if_pos h3, ←h1]
    assumption

syntax "unfold_expand_aux" : tactic
macro_rules
  | `(tactic| unfold_expand_aux) =>
    `(tactic| repeat unfold Polynomial.CoeffList.expandAux)

end Semiring

end Polynomial.CoeffList

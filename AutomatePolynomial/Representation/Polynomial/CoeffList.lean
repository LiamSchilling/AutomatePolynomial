import AutomatePolynomial.Representation.Polynomial.Defs
import AutomatePolynomial.Hyperlist.Lemmas

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

theorem reps_zero :
    reps (0 : R[X]) [] := by
  unfold reps; simp

theorem reps_C :
    reps (C c : R[X]) [c] := by
  unfold reps; intro n; rw[coeff_C]; cases n <;> simp

theorem reps_X :
    reps (X : R[X]) [0, 1] := by
  unfold reps; intro n; rw[coeff_X]; cases n <;> simp; rename_i n; cases n <;> simp

theorem reps_tail :
    reps (p : R[X]) (c :: L) → reps p.tail L := by
  intro h n; apply h

theorem eq_of_reps_cons :
    reps (p : R[X]) (c :: L) → p = C c + p.tail * X := by
  intro h; ext n; cases n
  . simp; apply h
  . unfold tail; simp

theorem eq_of_reps_nil :
    reps (p : R[X]) [] → p = 0 := by
  intro h; apply leadingCoeff_eq_zero.mp; apply h

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

theorem reps_mulC {L : List R}
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
  induction L1 generalizing p with
  | nil =>
    rw[eq_of_reps_nil h1]
    intro n
    cases Nat.decLt n L2.length.pred <;> (rename_i h; simp at h)
    . rw[List.getElem?_eq_none]; simp; simpa
    . rw[(List.getElem?_eq_some_getElem_iff (by simpa)).mpr trivial]; simp
  | cons c L1' ih =>
    rw[eq_of_reps_cons h1, mul_comm _ X, right_distrib, mul_assoc]
    apply reps_add
    . apply reps_mulC; assumption
    . apply reps_mulX; apply ih; apply reps_tail; assumption

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

theorem reps_power {L : List R} (h : reps p L) :
    reps (p ^ n) (power n L) := by
  induction n with
  | zero => exact reps_C
  | succ n' ih => rw[pow_succ]; exact reps_mul ih h

end CommSemiring

section Semiring

variable [Semiring R]

/-- Asserts that a coefficient list has no zeros on leading terms -/
@[simp]
def normal [DecidablePred (Eq 0 : R → Prop)] (L : List R) :=
  match L.reverse with | [] => True | c :: _ => 0 ≠ c

/-- Coefficient list operation to drop zeros on leading terms -/
@[simp]
def normalize [DecidablePred (Eq 0 : R → Prop)] (L : List R) :=
  (L.reverse.dropWhile (Eq 0 : R → Prop)).reverse

theorem getD_normalize [DecidablePred (Eq 0 : R → Prop)] {L : List R} {n : ℕ} :
    L[n]?.getD 0 = (normalize L)[n]?.getD 0 := by
  induction L generalizing n with
  | nil => simp
  | cons c L' ih =>
    simp at ih
    cases n <;> (
      simp; try rw[ih]
      induction L'.reverse with
      | nil => by_cases h: 0 = c <;> simp[h]
      | cons c' L'' ih' =>
        by_cases h: 0 = c'
        . rw[←h, show 0 :: L'' ++ [c] = 0 :: (L'' ++ [c]) by rfl]; simp; exact ih'
        . simp[h] )

theorem reps_normalize [DecidablePred (Eq 0 : R → Prop)] {L : List R}
    (h : reps p L) :
    reps p (normalize L) := by
  unfold reps; intro; rw[←getD_normalize]; apply h

theorem normal_normalize [DecidablePred (Eq 0 : R → Prop)] {L : List R} :
    normal (normalize L) := by
  induction L with
  | nil => simp
  | cons c L ih =>
    simp [List.dropWhile_append]
    split <;> rename_i tl h
    <;> by_cases hZero : ∀ x ∈ L, 0 = x
    · simp
    · simp
    · contrapose! h
      have h' : (∀ x ∈ L, 0 = x) = True := by simp [hZero]; exact hZero
      simp [h']
      sorry
      -- simp [List.length_drop]
    · contrapose! h
      have h' : (∀ x ∈ L, 0 = x) = False := by simp [hZero]
      simp [h', h]
      sorry

theorem normalize_idem [DecidablePred (Eq 0 : R → Prop)] {L : List R} :
    normal L → L = normalize L := by
  intro h; simp at h
  cases hh : L.reverse
  . rw[List.reverse_eq_nil_iff.mp hh]; simp
  . simp; rw[hh, List.dropWhile_cons_of_neg, ←hh, List.reverse_reverse]; rw[hh] at h; simp; exact h

/-- Retrieves the degree from a normal coefficient list -/
@[simp]
def degree_if_normal (L : List R) :=
  match L.length with | 0 => (⊥ : WithBot ℕ) | l' + 1 => some l'

theorem degree_eq_of_normal [DecidablePred (Eq 0 : R → Prop)] {L : List R}
    (h1 : normal L) (h2 : reps p L) :
    p.degree = degree_if_normal L := by
  cases L
  . rw[leadingCoeff_eq_zero.mp (h2 p.natDegree)]; rfl
  . rename_i c L'; revert h2 h1
    rw[←List.reverse_reverse L']; cases L'.reverse <;> (intro h1 h2; simp at h1 h2)
    . apply degree_eq_of_le_of_coeff_ne_zero
      . sorry
      . rw[h2]; intro h3; symm at h3; contradiction
    . rename_i c' L''
      apply degree_eq_of_le_of_coeff_ne_zero
      . sorry
      . rw[h2]
        suffices h3 : (c :: (L''.reverse ++ [c']))[(c' :: L'').reverse.length]?.getD 0 = c' from by
          rw[h3]; symm; exact h1
        rw[←List.reverse_reverse (c :: _), List.getElem?_reverse]
        all_goals simp

/-- Retrieves the leading coefficient from a normal coefficient list -/
@[simp]
def leadingCoeff_if_normal (L : List R) :=
  match L.reverse with | [] => 0 | c :: _ => c

theorem leadingCoeff_eq_of_normal [DecidablePred (Eq 0 : R → Prop)] {L : List R}
    (h1 : normal L) (h2 : reps p L) :
    p.leadingCoeff = leadingCoeff_if_normal L := by
  unfold leadingCoeff; unfold natDegree; rw[degree_eq_of_normal h1 h2, h2]; simp
  rw[←List.reverse_reverse L]; cases L.reverse <;> simp[WithBot.unbotD, WithBot.recBotCoe]

/-- given coefficients [c0, c1, ... cm]
computes polynomial (cm*x^m+n + ... c1*x^1+n + c0*x^n) -/
noncomputable def expand (L : List R) (n : ℕ) :=
  match L with
  | [] => 0
  | c :: L => expand L n.succ + C c * X ^ n

theorem expand_coeff
    {L : List R} {N : ℕ} :
    (expand L N).coeff n =
    if n < N then 0 else L[n - N]?.getD 0 := by
  cases L
  . unfold expand
    cases inferInstanceAs (Decidable (n < N)) <;> rename_i h
    . rw[if_neg h]; rfl
    . rw[if_pos h]; rfl
  . unfold expand; simp; rw[expand_coeff]
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

theorem expand_eq
    {p : R[X]} {L : List R} {N : ℕ} :
    (∀ n, n < N → p.coeff n = 0) →
    (∀ n, p.coeff (N + n) = L[n]?.getD 0) →
    p = expand L N := by
  intro h1 h2; apply ext; intro n
  rw[expand_coeff]
  cases inferInstanceAs (Decidable (n < N)) <;> rename_i h3
  . rw[if_neg h3, ←h2]; simp at h3
    apply congrArg; symm; apply Nat.add_sub_of_le; assumption
  . rw[if_pos h3, ←h1]
    assumption

syntax "poly_unfold_expand" : tactic
macro_rules
  | `(tactic| poly_unfold_expand) =>
    `(tactic| repeat unfold Polynomial.CoeffList.expand)

end Semiring

end Polynomial.CoeffList

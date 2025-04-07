import AutomatePolynomial.Hyperlist.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import AutomatePolynomial.Reflection.NormalForm

namespace Polynomial

variable [Semiring R] in
def is_coeff (p : R[X]) (cs : List R) := ∀ {n}, p.coeff n = cs[n]?.getD 0

namespace Coeffs

-- add coefficient lists
variable [Semiring R] in
@[simp]
def addAux (cs1 cs2 : List R) :=
  List.match_zipWith (. + .) cs1 cs2 0 0

variable [Semiring R] in
lemma addAux_length
    {cs1 cs2 : List R} :
    (addAux cs1 cs2).length =
    max cs1.length cs2.length := by
  apply List.length_match_zipWith

variable [Semiring R] in
lemma addAux_eq
    {n : ℕ} {cs1 cs2 : List R} :
    (addAux cs1 cs2)[n]?.getD 0 =
    cs1[n]?.getD 0 + cs2[n]?.getD 0 := by
  nth_rw 1 [←show 0 + 0 = (0 : R) by simp]
  apply List.getElem?_getD_match_zipWith

variable [Semiring R] in
lemma addAux_rep
    {p q : R[X]} {cs1 cs2 : List R}
    (h1 : p.is_coeff cs1) (h2 : q.is_coeff cs2) :
    (p + q).is_coeff (addAux cs1 cs2) := by
  intro; rw[Coeffs.addAux_eq, ←h1, ←h2]; simp

-- multiply by constant
variable [Semiring R] in
@[simp]
def mulCAux (c : R) (cs : List R) :=
  cs.map (c * .)

variable [Semiring R] in
lemma mulCAux_length
    {c : R} {cs : List R} :
    (mulCAux c cs).length =
    cs.length := by
  simp

variable [Semiring R] in
lemma mulCAux_eq
    {n : ℕ} {c : R} {cs : List R} :
    (mulCAux c cs)[n]?.getD 0 =
    c * cs[n]?.getD 0 := by
  simp
  cases inferInstanceAs (Decidable (n < cs.length)) <;> rename_i h
  . simp at h
    rw[List.getElem?_eq_none]; simp; assumption
  . rw[(List.getElem?_eq_some_getElem_iff h).mpr trivial]; simp

variable [Semiring R] in
lemma mulCAux_rep
    {c : R} {p : R[X]} {cs : List R}
    (h : p.is_coeff cs) :
    (C c * p).is_coeff (mulCAux c cs) := by
  intro; rw[Coeffs.mulCAux_eq, ←h]; simp

-- multiply by X
variable [Semiring R] in
@[simp]
def mulXAux (cs : List R) :=
  0 :: cs

variable [Semiring R] in
lemma mulXAux_length
    {cs : List R} :
    (mulXAux cs).length =
    cs.length + 1 := by
  simp

variable [Semiring R] in
lemma mulXAux_eq
    {n : ℕ} {cs : List R} :
    (mulXAux cs)[n]?.getD 0 =
    match n with
    | 0 => 0
    | n + 1 => cs[n]?.getD 0 := by
  cases n <;> simp

variable [Semiring R] in
lemma mulXAux_rep
    {p : R[X]} {cs : List R}
    (h : p.is_coeff cs) :
    (X * p).is_coeff (mulXAux cs) := by
  intro n; rw[Coeffs.mulXAux_eq]; cases n <;> simp; rw[←h]

-- multiply by power of X
variable [Semiring R] in
@[simp]
def mulXPowAux (n : ℕ) (cs : List R) :=
  match n with
  | 0 => cs
  | n + 1 => mulXAux (mulXPowAux n cs)

variable [Semiring R] in
lemma mulXPowAux_length
    {n : ℕ} {cs : List R} :
    (mulXPowAux n cs).length =
    n + cs.length := by
  cases n <;> rename_i n
  . simp
  . unfold mulXPowAux; rw[mulXAux_length, mulXPowAux_length, add_assoc]; nth_rw 2 [add_comm]; rw[add_assoc]

variable [CommSemiring R] in
lemma mulXPowAux_rep
    {n : ℕ} {p : R[X]} {cs : List R}
    (h : p.is_coeff cs) :
    (X ^ n * p).is_coeff (mulXPowAux n cs) := by
  cases n <;> rename_i n
  . simpa
  . unfold mulXPowAux; unfold is_coeff; intro N
    rw[mulXAux_eq]; cases N;
    . simp
    . simp; rw[←mulXPowAux_rep h]
      rw[pow_succ]; nth_rw 2 [mul_comm]; rw[mul_assoc]
      simp

-- multiply coefficient lists
variable [Semiring R] in
@[simp]
def mulAux (cs1 cs2 : List R) :=
  match cs1 with
  | [] => List.replicate cs2.length.pred 0
  | c :: cs1 => addAux (mulXAux (mulAux cs1 cs2)) (mulCAux c cs2)

variable [Semiring R] in
lemma mulAux_length
    {cs1 cs2 : List R} :
    (mulAux cs1 cs2).length =
    cs1.length + cs2.length.pred := by
  cases cs1
  . simp
  . unfold mulAux; rw[addAux_length]; simp; rw[mulAux_length]
    rw[Nat.max_eq_left]
    apply add_right_comm; rw[add_assoc]; apply le_add_left
    apply Nat.le_add_of_sub_le; apply le_of_eq; rfl

variable [CommSemiring R] in
lemma mulAux_rep
    {p q : R[X]} {cs1 cs2 : List R}
    (h1 : p.is_coeff cs1) (h2 : q.is_coeff cs2) :
    (p * q).is_coeff (mulAux cs1 cs2) := by
  cases cs1
  . rw[leadingCoeff_eq_zero.mp h1]; unfold is_coeff; intro n; simp
    sorry
  . sorry

-- power of a coefficient list
variable [Semiring R] in
@[simp]
def powAux (n : ℕ) (cs : List R) :=
  match n with
  | 0 => [1]
  | n + 1 => mulAux (powAux n cs) cs

variable [Semiring R] in
lemma powAux_length
    {n : ℕ} {cs2 : List R} :
    (powAux n cs2).length =
    n * cs2.length.pred + 1 := by
  cases n
  . simp
  . unfold powAux; rw[mulAux_length, powAux_length]
    rw[add_comm, ←add_assoc]
    nth_rw 2 [add_comm]
    rw[mul_comm, ←Nat.mul_succ, mul_comm]

variable [CommSemiring R] in
lemma powAux_rep
    {n : ℕ} {p : R[X]} {cs : List R}
    (h : p.is_coeff cs) :
    (p ^ n).is_coeff (powAux n cs) := by
  cases n
  . simp; unfold is_coeff; intro n; rw[coeff_one]
    cases n <;> simp
  . rw[pow_succ]; unfold powAux; apply mulAux_rep; exact powAux_rep h; exact h

-- given coefficients [c0, c1, ... cn]
-- computes abstract polynomial (cn*x^n + ... c1*x + c0)
variable [Semiring R] in
noncomputable def expandAux (cs : List R) (n : ℕ) :=
  match cs with
  | [] => 0
  | c :: cs => expandAux cs n.succ + C c * X ^ n

variable [Semiring R] in
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

variable [Semiring R] in
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

end Coeffs

end Polynomial

-- fully unfold expand call
syntax "unfold_expand_aux" : tactic
macro_rules
  | `(tactic| unfold_expand_aux) =>
    `(tactic| repeat unfold Polynomial.Coeffs.expandAux)

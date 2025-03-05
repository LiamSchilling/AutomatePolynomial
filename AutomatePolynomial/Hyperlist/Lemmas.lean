import AutomatePolynomial.Hyperlist.Basic
import Mathlib.Tactic.NthRewrite

namespace List

lemma length_extend
    {L : List α} :
    (extend L N a₀).length =
    max L.length N := by
  simp
  cases inferInstanceAs (Decidable (L.length ≤ N)) <;> rename_i h
  . simp at h
    rw[Nat.max_eq_left (le_of_lt h)]
    rw[Nat.sub_eq_zero_of_le (le_of_lt h)]; rfl
  . rw[Nat.max_eq_right h]
    rw[Nat.add_sub_of_le h]

lemma getElem?_extend
    {n : ℕ} {L : List α} :
    (extend L N a₀)[n]? =
    match L[n]? with
    | none => if n < N then some a₀ else none
    | some a => some a := by
  cases h1 : L[n]?
  . cases inferInstanceAs (Decidable (n < N)) <;> rename_i h2
    . rw[if_neg h2]
      simp at h2
      apply getElem?_eq_none_iff.mpr
      rw[length_extend]; simp; constructor
      . apply getElem?_eq_none_iff.mp; assumption
      . assumption
    . rw[if_pos h2]
      unfold extend; rw[getElem?_append_right]
      rw[getElem?_replicate_of_lt]
      apply Nat.sub_lt_sub_right
      . apply getElem?_eq_none_iff.mp; assumption
      . assumption
      apply getElem?_eq_none_iff.mp; assumption
  . unfold extend; rw[getElem?_append_left]
    assumption
    apply isSome_getElem?.mp; rw[h1]; trivial

lemma getElem?_getD_extend
    {n : ℕ} {L : List α} :
    (extend L N a₀)[n]?.getD a₀ =
    L[n]?.getD a₀
    := by
  rw[getElem?_extend]
  cases L[n]?
  . cases inferInstanceAs (Decidable (n < N)) <;> rename_i h
    . rw[if_neg h]
    . rw[if_pos h]; rfl
  . rfl

lemma length_match_zipWith
    {L1 : List α} {L2 : List β} :
    (match_zipWith f L1 L2 a₀ b₀).length =
    max L1.length L2.length := by
  simp

lemma getElem?_match_zipWith
    {n : ℕ} {L1 : List α} {L2 : List β} :
    (match_zipWith f L1 L2 a₀ b₀)[n]? =
    match L1[n]?, L2[n]? with
    | some a, some b => some (f a b)
    | some a, none => some (f a b₀)
    | none, some b => some (f a₀ b)
    | none, none => none := by
  unfold match_zipWith; unfold match_extend
  rw[getElem?_zipWith, getElem?_extend, getElem?_extend]
  cases h1 : L1[n]? <;> cases h2 : L2[n]?
  . rw[if_neg]
    simp; constructor
    all_goals apply getElem?_eq_none_iff.mp; assumption
  . nth_rw 1 [if_pos]
    simp; right
    apply isSome_getElem?.mp; rw[h2]; trivial
  . nth_rw 2 [if_pos]
    simp; left
    apply isSome_getElem?.mp; rw[h1]; trivial
  . rfl

lemma getElem?_getD_match_zipWith
    {n : ℕ} {L1 : List α} {L2 : List β} :
    (match_zipWith f L1 L2 a₀ b₀)[n]?.getD (f a₀ b₀) =
    f (L1[n]?.getD a₀) (L2[n]?.getD b₀) := by
  rw[getElem?_match_zipWith]
  cases L1[n]? <;> cases L2[n]? <;> rfl

end List

import AutomatePolynomial.Hyperlist.Basic

/-!
# Hyperlist Lemmas

We show that mapping functions on `Hyperlist`
(`map`, `zipWith`, `zipWithPad`, `nodupsMerge_zipWithPad`)
behave as expected.
For "Pad" functions, importantly,
constants can be extrapolated past the finite bounds of the structure,
effectively modeling finitely supported functions.

 -/

namespace List

/-- The length of `zipWithPad` on lists is the max of their lengths -/
theorem length_zipWithPad {f : α → β → γ} :
    (zipWithPad f a₀ b₀ L1 L2).length =
    max L1.length L2.length := by
  cases L1 <;> cases L2 <;> simp <;> rw[length_zipWithPad] <;> simp

/-- `List.getElem?` on `zipWithPad`
can be simplified to `List.getElem?` on the lists -/
theorem getElem?_zipWithPad {f : α → β → γ} {n : ℕ} :
    (zipWithPad f a₀ b₀ L1 L2)[n]? =
    match L1[n]?, L2[n]? with
    | some a, some b => some (f a b)
    | some a, none => some (f a b₀)
    | none, some b => some (f a₀ b)
    | none, none => none := by
  sorry

/-- `List.getElem? ∘ Option.getD` on `zipWithPad`
can be simplified to `List.getElem? ∘ Option.getD` on the lists,
extrapolating the default values -/
theorem getD_zipWithPad {f : α → β → γ} {n : ℕ} :
    (zipWithPad f a₀ b₀ L1 L2)[n]?.getD (f a₀ b₀) =
    f (L1[n]?.getD a₀) (L2[n]?.getD b₀) := by
  rw[getElem?_zipWithPad]; cases L1[n]? <;> cases L2[n]? <;> rfl

end List

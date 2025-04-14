import Mathlib.Data.Set.Basic

/-!
# Normalizer

A `Normalizer` gives a type a normal form and a method of conversion to normal form.

 -/

/-- Gives a type a normal form and a method of conversion to normal form -/
structure Normalizer (α : Type*) where
  Normal : Set α
  normalize : α → Normal
  normalize_idem : ∀ a ∈ Normal, a = normalize a

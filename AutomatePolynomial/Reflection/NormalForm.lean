import Mathlib.Data.Set.Basic

-- establishes a set of normal forms and computable method of conversion
class Normalizer (α : Type*) where
  Normal : Set α
  normalize : α → Normal
  normalize_idempotent : ∀ a ∈ Normal, a = normalize a

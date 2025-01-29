import Mathlib.Algebra.Module.Defs

-- similar to NoZeroDivisors, asserts that no members have additive inverses
class NoAdditiveInverses (α : Type*) [Add α] [Zero α] where
  eq_zero_and_eq_zero_of_add_eq_zero : ∀ {a b : α}, a + b = 0 → a = 0 ∧ b = 0

-- no nontrivial natural numbers have additive inverses
instance : NoAdditiveInverses ℕ where
  eq_zero_and_eq_zero_of_add_eq_zero := Nat.eq_zero_of_add_eq_zero

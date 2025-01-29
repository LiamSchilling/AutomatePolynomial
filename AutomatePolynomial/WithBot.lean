import Mathlib.Order.WithBot

namespace WithBot

-- reflexivity of ≤ over WithBot
theorem le_self [LE α] (h1 : ∀ b : α, b ≤ b) {a : WithBot α} : a ≤ a :=
  fun b h2 => Exists.intro b (And.intro h2 (h1 b))

end WithBot

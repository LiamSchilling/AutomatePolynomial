import Mathlib.Order.WithBot

variable {α β γ : Type*} [LE α]

namespace WithBot

-- reflexivity of ≤ over WithBot
lemma le_self (h1 : ∀ b : α, b ≤ b) {a : WithBot α} : a ≤ a :=
  fun b h2 => Exists.intro b (And.intro h2 (h1 b))

end WithBot

namespace Option

-- reflexivity of ≤ over WithBot
def zip (f : α → β → γ) (A : Option α) (B : Option β) :=
  (Option.map (fun b => Option.map (fun a => f a b) A) B).getD none

end Option

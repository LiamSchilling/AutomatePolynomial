import AutomatePolynomial.Util.WithBot

variable {α β γ : Type*}

inductive Hyperlist (α : Type*) where
| leaf : α → Hyperlist α
| node : List (Hyperlist α) → Hyperlist α

@[simp] def Hyperlist.nil : Hyperlist α := node []
@[simp] def Hyperlist.wrap (L : Hyperlist α) : Hyperlist α := node [L]

namespace List

@[simp]
def fold_head (f : α → β) (g : List α → List β) (L : List α) :=
  match L with
  | [] => g []
  | a :: as => f a :: g as

@[simp]
def extend (L : List α) n a₀ :=
  L ++ replicate (n - L.length) a₀

@[simp]
def match_extend (L1 : List α) (L2 : List β) a₀ b₀ :=
  let len := max L1.length L2.length
  (L1.extend len a₀, L2.extend len b₀)

@[simp]
def match_zipWith (f : α → β → γ) (L1 : List α) (L2 : List β) a₀ b₀ :=
  let (L1, L2) := match_extend L1 L2 a₀ b₀
  zipWith f L1 L2

end List

namespace Hyperlist

@[simp]
def fold
    (f : α → β) (g : List (Hyperlist α) → List (Hyperlist β))
    (L : Hyperlist α) :=
  match L with
  | leaf a => leaf (f a)
  | node L => node (g L)

@[simp]
def fold_zip
    (f : α → β → γ) (g : List (Hyperlist α) → List (Hyperlist β) → List (Hyperlist γ))
    (L1 : Hyperlist α) (L2 : Hyperlist β) :=
  match L1, L2 with
  | leaf a1, leaf a2 => leaf (f a1 a2)
  | leaf a1, node L2 => node (g [leaf a1] L2)
  | node L1, leaf a2 => node (g L1 [leaf a2])
  | node L1, node L2 => node (g L1 L2)

/-
partial def merge_and_match_zipWith
    (f : α → β → γ)
    (I1 I2 :  List σ)
    (L1 : Hyperlist α) (L2 : Hyperlist β)
    (a₀ : α) (b₀ : β)
    (cmp : σ → σ → Ordering := by exact fun a b => compare a b)
    : Hyperlist γ :=
  let even I1 I2 := fold_zip f (List.match_zipWith (merge_and_match_zipWith f I1 I2 . . a₀ b₀ cmp) . . nil nil) L1 L2
  let left I1 I2 := fold (f . b₀) (List.fold_head (merge_and_match_zipWith f I1 I2 . L2 a₀ b₀ cmp) sorry .) L1
  let right I2 I2 := fold (f a₀ .) (List.fold_head sorry sorry .) L2
  match I1, I2 with
  | [], [] => even [] []
  | i :: I, [] => left I []
  | [], i :: I => right [] I
  | i1 :: I1, i2 :: I2 =>
  match cmp i1 i2 with
  | .lt => left I1 (i2 :: I2)
  | .gt => right (i2 :: I2) I2
  | .eq => even I1 I2
  -/

end Hyperlist

import AutomatePolynomial.Util.WithBot
import Mathlib.Data.Tree.Basic

inductive Hyperlist (α : Type*) where
| mk : α → Tree α → Hyperlist α

open Tree Hyperlist

variable {α β γ σ : Type*}

namespace Tree

@[simp]
def step : Tree α → Option (Hyperlist α)
| nil => none
| node a TL _ => some (mk a TL)

@[simp]
def slice : Tree α → Tree α
| nil => nil
| node _ _ DM => DM

---------

@[simp]
def length : Tree α → ℕ
| nil => 0
| node _ TL _ => TL.length + 1

@[simp]
def replicate : ℕ → α → Tree α
| 0, _ => nil
| n + 1, a => node a (replicate n a) nil

@[simp]
def append : Tree α → Tree α → Tree α
| nil, T => T
| node a TL DM, T => node a (TL.append T) DM

@[simp]
def extend : Tree α → ℕ → α → Tree α
| T, n, a₀ => T.append (replicate (n - T.length) a₀)

@[simp]
def match_extend (T1 : Tree α) (T2 : Tree β) (a₀ : α) (b₀ : β) :=
  let len := max T1.length T2.length
  (T1.extend len a₀, T2.extend len b₀)

end Tree

namespace Hyperlist

@[simp]
def step : Hyperlist α → Option (Hyperlist α)
| mk _ T => T.step

@[simp]
def slice : Hyperlist α → Hyperlist α
| mk a T => mk a T.slice

@[simp]
def node : Option (Hyperlist α) → Hyperlist α → Hyperlist α
| none, mk a DM => mk a DM
| some (mk a_ TL), mk a DM => mk a (Tree.node a_ TL DM)

@[simp]
def map_node
    (f : Hyperlist α → Hyperlist β)
    (g : Hyperlist α → Hyperlist β)
    (L : Hyperlist α) :=
  node (Option.map f L.step) (g L.slice)

@[simp]
def zip_node
    (f : Hyperlist α → Hyperlist β → Hyperlist γ)
    (g : Hyperlist α → Hyperlist β → Hyperlist γ)
    (L1 : Hyperlist α) (L2 : Hyperlist β) :=
  node (Option.zip f L1.step L2.step) (g L1.slice L2.slice)

----------

@[simp]
def get_head : Hyperlist α → α
| mk a _ => a

@[simp]
def get_step? (L : Hyperlist α) (i : ℕ) :=
  Fin.foldrM i (fun _ acc => acc.step) L

@[simp]
def get_slice? (L : Hyperlist α) (is : List ℕ) :=
  List.foldlM (fun acc i => Option.map slice (acc.get_step? i)) L is

@[simp]
def get? (L : Hyperlist α) (is : List ℕ) :=
  Option.map get_head (L.get_slice? is)

----------

@[simp]
def pred_length : Hyperlist α → ℕ
| mk _ T => T.length

@[simp]
def length : Hyperlist α → ℕ
| L => L.pred_length.succ

@[simp]
def map : (α → β) → Hyperlist α → Hyperlist β
| f, mk a T => mk (f a) (T.map f)

@[simp]
def replicate : ℕ → α → Hyperlist α
| n, a => mk a (Tree.replicate n a)

@[simp]
def append : Hyperlist α → Tree α → Hyperlist α
| mk a T1, T2 => mk a (T1.append T2)

@[simp]
def extend_succ : Hyperlist α → ℕ → α → Hyperlist α
| mk a T, n, a₀ => mk a (T.extend n a₀)

@[simp]
def extend : Hyperlist α → ℕ → α → Hyperlist α
| L, n, a₀ => L.extend_succ n.pred a₀

@[simp]
def match_extend (L1 : Hyperlist α) (L2 : Hyperlist β) (a₀ : α) (b₀ : β) :=
  let pred_len := max L1.pred_length L2.pred_length
  (L1.extend_succ pred_len a₀, L2.extend_succ pred_len b₀)

@[simp]
def zipWith :
    (Hyperlist α → Hyperlist β → Hyperlist γ) →
    Hyperlist α → Hyperlist β →
    Hyperlist γ
| f, mk a (Tree.node a_ TL1 DM1), mk b (Tree.node b_ TL2 DM2) =>
  let ⟨c_, TL⟩ := zipWith f (mk a_ TL1) (mk b_ TL2)
  let ⟨c, DM⟩ := f (mk a DM1) (mk b DM2)
  mk c (Tree.node c_ TL DM)
| f, mk a _, mk b _ => mk (f (mk a nil) (mk b nil)).get_head nil

@[simp]
def match_zipWith
    (f : Hyperlist α → Hyperlist β → Hyperlist γ)
    (T1 : Hyperlist α) (T2 : Hyperlist β)
    (a₀ : α) (b₀ : β) :=
  let (T1, T2) := match_extend T1 T2 a₀ b₀
  zipWith f T1 T2

@[simp]
def merge_and_match_zipWith
    (f : α → β → γ)
    (I1 I2:  List σ)
    (L1 : Hyperlist α) (L2 : Hyperlist β)
    (a₀ : α) (b₀ : β)
    (cmp : σ → σ → Ordering := by exact fun a b => compare a b) :=
  match I1, I2 with
  | [], [] => mk (f L1.get_head L2.get_head) nil
  | [], _ :: I => map_node (map (f a₀ .)) (merge_and_match_zipWith f [] I L1 . a₀ b₀ cmp) L2
  | _ :: I, [] => map_node (map (f . b₀)) (merge_and_match_zipWith f I [] . L2 a₀ b₀ cmp) L1
  | i1 :: I1, i2 :: I2 =>
  match cmp i1 i2 with
  | .lt => map_node (map (f . b₀)) (merge_and_match_zipWith f I1 (i2 :: I2) . L2 a₀ b₀ cmp) L1
  | .gt => map_node (map (f a₀ .)) (merge_and_match_zipWith f (i1 :: I1) I2 L1 . a₀ b₀ cmp) L2
  | .eq => match_zipWith (merge_and_match_zipWith f I1 I2 . . a₀ b₀ cmp) L1 L2 a₀ b₀

end Hyperlist

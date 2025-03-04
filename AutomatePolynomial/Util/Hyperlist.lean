import AutomatePolynomial.Util.WithBot
import Mathlib.Data.Tree.Basic

-- representation of unbounded tensors
-- left subtree is increase in current dimension
-- right subtree begins traversing in next dimension
-- value at a node encodes the successor index (trees are rootless)
-- Hyperlist wraps such a rootless tree with a root
inductive Hyperlist (α : Type*) where
| mk : α → Tree α → Hyperlist α

namespace List

-- BASIC OPERATIONS

-- extend length by appending a replicated element
@[simp]
def extend : List α → ℕ → α → List α
| L, n, a₀ => L ++ replicate (n - L.length) a₀

-- extend the shorter to match the length of the longer
@[simp]
def match_extend (L1 : List α) (L2 : List β) (a₀ : α) (b₀ : β) :=
  let len := max L1.length L2.length
  (L1.extend len a₀, L2.extend len b₀)

-- ADVANCED OPERATIONS

-- zip after extending to match
@[simp]
def match_zipWith
    (f : α → β → γ)
    (L1 : List α) (L2 : List β)
    (a₀ : α) (b₀ : β) :=
  let (L1, L2) := match_extend L1 L2 a₀ b₀
  zipWith f L1 L2

-- merge strictly sorted lists into a strictly sorted list
@[simp]
def merge_nodups
    (L1 : List σ) (L2 : List σ)
    (cmp : σ → σ → Ordering := by exact fun a b => compare a b) :=
  match L1, L2 with
  | [], [] => []
  | [], I => I
  | I, [] => I
  | i1 :: I1, i2 :: I2 =>
  match cmp i1 i2 with
  | .lt => i1 :: merge_nodups I1 (i2 :: I2) cmp
  | .gt => i2 :: merge_nodups (i1 :: I2) I2 cmp
  | .eq => i1 :: merge_nodups I1 I2 cmp

end List

namespace Tree

-- DECONSTRUCTION

-- delete the head index slice (like tail)
@[simp]
def step : Tree α → Option (Hyperlist α)
| nil => none
| node a TL _ => some (.mk a TL)

-- get the slice at the head index
@[simp]
def slice : Tree α → Tree α
| nil => nil
| node _ _ DM => DM

-- BASIC OPERATIONS

-- length of leftmost chain
@[simp]
def length : Tree α → ℕ
| nil => 0
| node _ TL _ => TL.length + 1

-- copy along the nodes of leftmost chain
@[simp]
def replicate : ℕ → α → Tree α
| 0, _ => nil
| n + 1, a => node a (replicate n a) nil

-- append second leftmost chain to start of first leftmost chain
@[simp]
def append : Tree α → Tree α → Tree α
| nil, T => T
| node a TL DM, T => node a (TL.append T) DM

-- extend leftmost chain to length by appending a replicated single
@[simp]
def extend : Tree α → ℕ → α → Tree α
| T, n, a₀ => T.append (replicate (n - T.length) a₀)

-- extend the shorter to match the length of the longer
@[simp]
def match_extend (T1 : Tree α) (T2 : Tree β) (a₀ : α) (b₀ : β) :=
  let len := max T1.length T2.length
  (T1.extend len a₀, T2.extend len b₀)

end Tree

namespace Hyperlist

-- DECONSTRUCTION

-- delete the head index slice (like tail)
@[simp]
def step : Hyperlist α → Option (Hyperlist α)
| mk _ T => T.step

-- get the slice at the head index
@[simp]
def slice : Hyperlist α → Hyperlist α
| mk a T => mk a T.slice

-- CONSTRUCTION

-- construct from tail and head slice
@[simp]
def node : Option (Hyperlist α) → Hyperlist α → Hyperlist α
| none, mk a DM => mk a DM
| some (mk a_ TL), mk a DM => mk a (.node a_ TL DM)

-- map functions on tail (f) and head (g)
@[simp]
def map_node
    (f : Hyperlist α → Hyperlist β)
    (g : Hyperlist α → Hyperlist β)
    (L : Hyperlist α) :=
  node (Option.map f L.step) (g L.slice)

-- zip functions on tail (f) and head (g)
@[simp]
def zip_node
    (f : Hyperlist α → Hyperlist β → Hyperlist γ)
    (g : Hyperlist α → Hyperlist β → Hyperlist γ)
    (L1 : Hyperlist α) (L2 : Hyperlist β) :=
  node (Option.zip f L1.step L2.step) (g L1.slice L2.slice)

-- RETRIEVAL

-- 0 index in all dimensions
@[simp]
def get_head : Hyperlist α → α
| mk a _ => a

-- tail after i deletions
@[simp]
def get_step? (L : Hyperlist α) (i : ℕ) :=
  Fin.foldrM i (fun _ => step) L

-- slice after stepping is[j] in each jth dimension
@[simp]
def get_slice? (L : Hyperlist α) (is : List ℕ) :=
  List.foldlM (fun acc i => Option.map slice (acc.get_step? i)) L is

-- is[j] index in each jth dimension
@[simp]
def get? (L : Hyperlist α) (is : List ℕ) :=
  Option.map get_head (L.get_slice? is)

-- BASIC OPERATIONS

-- predecessor of length in 0th dimension
@[simp]
def pred_length : Hyperlist α → ℕ
| mk _ T => T.length

-- length in 0th dimension (≠ 0)
@[simp]
def length : Hyperlist α → ℕ
| L => L.pred_length.succ

-- map by element
@[simp]
def map : (α → β) → Hyperlist α → Hyperlist β
| f, mk a T => mk (f a) (T.map f)

-- 1D list of n.succ length
@[simp]
def replicate_succ : ℕ → α → Hyperlist α
| n, a => mk a (Tree.replicate n a)

-- append along 0th dimension
@[simp]
def append : Hyperlist α → Tree α → Hyperlist α
| mk a T1, T2 => mk a (T1.append T2)

-- extend along 0th dimension to length n.succ
@[simp]
def extend_succ : Hyperlist α → ℕ → α → Hyperlist α
| mk a T, n, a₀ => mk a (T.extend n a₀)

-- extend along 0th dimension to length n
@[simp]
def extend : Hyperlist α → ℕ → α → Hyperlist α
| L, n, a₀ => L.extend_succ n.pred a₀

-- extend in 0th dimension to same length
@[simp]
def match_extend (L1 : Hyperlist α) (L2 : Hyperlist β) (a₀ : α) (b₀ : β) :=
  let pred_len := max L1.pred_length L2.pred_length
  (L1.extend_succ pred_len a₀, L2.extend_succ pred_len b₀)

-- ADVANCED OPERATIONS

-- zip slices along 0th dimension
@[simp]
def zipWith :
    (Hyperlist α → Hyperlist β → Hyperlist γ) →
    Hyperlist α → Hyperlist β →
    Hyperlist γ
| f, mk a (.node a_ TL1 DM1), mk b (.node b_ TL2 DM2) =>
  let ⟨c_, TL⟩ := zipWith f (mk a_ TL1) (mk b_ TL2)
  let ⟨c, DM⟩ := f (mk a DM1) (mk b DM2)
  mk c (.node c_ TL DM)
| f, mk a _, mk b _ =>
  let ⟨c, _⟩ := f (mk a .nil) (mk b .nil)
  mk c .nil

-- zip slices after extending to match
@[simp]
def match_zipWith
    (f : Hyperlist α → Hyperlist β → Hyperlist γ)
    (L1 : Hyperlist α) (L2 : Hyperlist β)
    (a₀ : α) (b₀ : β) :=
  let (L1, L2) := match_extend L1 L2 a₀ b₀
  zipWith f L1 L2

-- zip in every dimension along dimension labels
-- consider missing dimensions as unwrapped slices
-- truncate when dimension labels end
@[simp]
def merge_and_match_zipWith
    (f : α → β → γ)
    (I1 I2 : List σ)
    (L1 : Hyperlist α) (L2 : Hyperlist β)
    (a₀ : α) (b₀ : β)
    (cmp : σ → σ → Ordering := by exact fun a b => compare a b) :=
  match I1, I2 with
  | [], [] => mk (f L1.get_head L2.get_head) .nil
  | [], _ :: I => map_node (map (f a₀ .)) (merge_and_match_zipWith f [] I L1 . a₀ b₀ cmp) L2
  | _ :: I, [] => map_node (map (f . b₀)) (merge_and_match_zipWith f I [] . L2 a₀ b₀ cmp) L1
  | i1 :: I1, i2 :: I2 =>
  match cmp i1 i2 with
  | .lt => map_node (map (f . b₀)) (merge_and_match_zipWith f I1 (i2 :: I2) . L2 a₀ b₀ cmp) L1
  | .gt => map_node (map (f a₀ .)) (merge_and_match_zipWith f (i1 :: I1) I2 L1 . a₀ b₀ cmp) L2
  | .eq => match_zipWith (merge_and_match_zipWith f I1 I2 . . a₀ b₀ cmp) L1 L2 a₀ b₀

end Hyperlist

import Mathlib.Data.List.Basic

/-!
# Hyperlists

A `Hyperlist` is a higher-dimensional list.

## Main declarations

* `Hyperlist`: A tree representation of lists
  with unbounded dimension and variable lengths
* `nodupsMerge_zipWithPad`: A powerful method for zipping hyperlists,
  taking into account dimension labels
  and accounting for all elements via default values

 -/

/-- A tree representation of lists
with unbounded dimension and variable lengths -/
inductive Hyperlist (α : Type u) where
| single : α → Hyperlist α
| list : List (Hyperlist α) → Hyperlist α

namespace List

/-- Applies `f` to corresponding elements, using `a₀` and `b₀` for elements without matches -/
@[simp]
def zipWithPad : (α → β → γ) → α → β → List α → List β → List γ
| _, _, _, [], [] => []
| f, a₀, b₀, [], b :: L2 => f a₀ b :: zipWithPad f a₀ b₀ [] L2
| f, a₀, b₀, a :: L1, [] => f a b₀ :: zipWithPad f a₀ b₀ L1 []
| f, a₀, b₀, a :: L1, b :: L2 => f a b :: zipWithPad f a₀ b₀ L1 L2

/-- Merges lists using `cmp`
to pick the least element first and omit components of equal pairs
(prioritising keeping the left component)

When both lists are strictly increasing, the result is `eraseDups` composed with `merge`. -/
@[simp]
def nodupsMerge
    (L1 L2 : List α)
    (cmp : α → α → Ordering := by exact compare) :=
  match L1, L2 with
  | [], L2' => L2'
  | L1', [] => L1'
  | a :: L1', b :: L2' =>
  match cmp a b with
  | .lt => a :: nodupsMerge L1' (b :: L2') cmp
  | .gt => b :: nodupsMerge (a :: L1') L2' cmp
  | .eq => a :: nodupsMerge L1' L2' cmp

end List

namespace Hyperlist

/-- Converts a higher-dimensional hyperlist into a list of lower-dimensional hyperlists,
raising the dimension for `single` when necessary -/
@[simp]
def toList : Hyperlist α → List (Hyperlist α)
| single a => [single a]
| list L => L

/-- The value at the `0` index, or `none` if it does not exist -/
@[simp]
def getRoot? : Hyperlist α → Option α
| single a => some a
| list [] => none
| list (H :: _) => H.getRoot?

/-- The value at index `I[d]` along each dimension `d`, or `none` if any `I[d]` is out-of-bounds -/
@[simp]
def getElem? : Hyperlist α → List ℕ → Option α
| H, [] => H.getRoot?
| H, i :: I => match H.toList[i]? with | none => none | some H' => H'.getElem? I

/-- Length of the top dimension -/
@[simp]
def length : Hyperlist α → ℕ
| single _ => 1
| list L => L.length

/-- Number of nodes, used to show well-founded recursion -/
def size : Hyperlist α → ℕ
| single _ => 1
| list L => List.foldl (. + size .) 0 L + 1

/-
/-- Sub-hyperlists are smaller than their parent hyperlists -/
theorem sub_size_le (L : List (Hyperlist α)) : ∀ H ∈ L, H.size < (list L).size := by
  sorry
-/

/-- Applies `f` to each element -/
@[simp]
def map : (α → β) → Hyperlist α → Hyperlist β
| f, single a => single (f a)
| f, list L => list (List.map (map f) L)

/-
/-- Applies `f` to corresponding elements -/
@[simp]
def zipWith : (α → β → γ) → Hyperlist α → Hyperlist β → Hyperlist γ
| f, single a, single b => single (f a b)
| _, single _, list [] => list []
| _, list [], single _ => list []
| f, single a, list (H2 :: _) =>
  zipWith f (single a) H2
| f, list (H1 :: _), single b =>
  zipWith f H1 (single b)
| f, list L1, list L2 =>
  list (List.zipWith (fun ⟨a, _⟩ ⟨b, _⟩ => zipWith f a b) L1.attach L2.attach)
termination_by _ H1 H2 => H1.size + H2.size
decreasing_by
  all_goals simp_wf
  any_goals apply sub_size_le; simp
  apply Nat.add_lt_add_of_le_of_lt; apply le_of_lt
  all_goals apply sub_size_le; assumption
-/

/-
/-- Applies `f` to corresponding elements, using `a₀` and `b₀` for elements without matches -/
@[simp]
def zipWithPad : (α → β → γ) → α → β → Hyperlist α → Hyperlist β → Hyperlist γ
| f, _, _, single a, single b => single (f a b)
| f, _, b₀, single a, list [] => single (f a b₀)
| f, a₀, _, list [], single b => single (f a₀ b)
| f, a₀, b₀, single a, list (H2 :: L2) =>
  list (zipWithPad f a₀ b₀ (single a) H2 :: List.map (map (f a₀ .)) L2)
| f, a₀, b₀, list (H1 :: L1), single b =>
  list (zipWithPad f a₀ b₀ H1 (single b) :: List.map (map (f . b₀)) L1)
| f, a₀, b₀, list L1, list L2 =>
  list (List.zipWithPad (zipWithPad f a₀ b₀) (single a₀) (single b₀) L1 L2)
termination_by _ _ _ H1 H2 => H1.size + H2.size
decreasing_by
  all_goals simp_wf
  any_goals apply sub_size_le; simp
  . sorry
-/

/-
/-- Applies `f` to corresponding elements,
merging according to dimension labels in strictly increasing `I1` and `I2`,
using `a₀` and `b₀` for elements without matches,
producing a hyperlist with dimension labels `nodupsMerge I1 I2` -/
def nodupsMerge_zipWithPad
    (f : α → β → γ) (a₀ : α) (b₀ : β)
    (I1 I2 : List σ) (H1 : Hyperlist α) (H2 : Hyperlist β)
    (cmp : σ → σ → Ordering := by exact compare) :=
  match I1, I2 with
  | [], _ => zipWithPad f a₀ b₀ H1 H2
  | _, [] => zipWithPad f a₀ b₀ H1 H2
  | j :: I1', k :: I2' =>
  match cmp j k with
  | .lt =>
    match H1 with
    | list (H1' :: L1) =>
      list (nodupsMerge_zipWithPad
        f a₀ b₀ I1' (k :: I2') H1' H2 cmp :: List.map (map (f . b₀)) L1 )
    | _ => nodupsMerge_zipWithPad f a₀ b₀ I1' (k :: I2') H1 H2 cmp
  | .gt =>
    match H2 with
    | list (H2' :: L2) =>
      list (nodupsMerge_zipWithPad
        f a₀ b₀ (j :: I1') I2' H1 H2' cmp :: List.map (map (f a₀ .)) L2 )
    | _ => nodupsMerge_zipWithPad f a₀ b₀ (j :: I1') I2' H1 H2 cmp
  | .eq =>
    match H1, H2 with
    | single a, single b => single (f a b)
    | single a, list [] => single (f a b₀)
    | list [], single b => single (f a₀ b)
    | single a, list (H2 :: L2) =>
      list (nodupsMerge_zipWithPad
        f a₀ b₀ I1' I2' (single a) H2 cmp :: List.map (map (f a₀ .)) L2 )
    | list (H1 :: L1), single b =>
      list (nodupsMerge_zipWithPad
        f a₀ b₀ I1' I2' H1 (single b) cmp :: List.map (map (f . b₀)) L1 )
    | list L1, list L2 =>
      list (List.zipWithPad
        (nodupsMerge_zipWithPad f a₀ b₀ I1' I2' . . cmp) (single a₀) (single b₀) L1 L2 )
-/

end Hyperlist

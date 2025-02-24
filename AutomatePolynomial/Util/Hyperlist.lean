import Mathlib.Data.List.Defs
import Mathlib.Order.Defs.LinearOrder

import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Data.Nat.Order.Lemmas

-- n-dimensional list structure
def Hyperlist (α : Type*) (n : ℕ) :=
  match n with
  | 0 => α
  | n + 1 => List (Hyperlist α n)

@[simp] def hl0 : α → Hyperlist α 0 := by unfold Hyperlist; exact id
@[simp] def hl0' : Hyperlist α 0 → α := by unfold Hyperlist; exact id
@[simp] def hlc : List (Hyperlist α n) → Hyperlist α (n + 1) := by rw[Hyperlist]; exact id
@[simp] def hlc' : Hyperlist α (n + 1) → List (Hyperlist α n) := by rw[Hyperlist]; exact id

namespace Hyperlist

-- minimal hyperlist
@[simp]
instance zero [Zero α] : Zero (Hyperlist α n) where
  zero :=
  match n with
  | 0 => hl0 0
  | _ + 1 => []

-- reverse in every dimension
@[simp]
def reverse (L : Hyperlist α n) : Hyperlist α n :=
  match n with
  | 0 => L
  | _ + 1 => (L.map reverse).reverse

-- map hyperlist by elements
@[simp]
def map (f : α → β) (L : Hyperlist α n) : Hyperlist β n :=
  match n with
  | 0 => f L
  | _ + 1 => List.map (map f) L

-- length of outermost dimension
-- none if dimension is 0
@[simp]
def length (L : Hyperlist α n) :=
  match n with
  | 0 => none
  | _ + 1 => some (List.length L)

-- list with the length of all lists at each layer
-- none if layers have lists with non-uniform lengths
def dimension (L : Hyperlist α n) :=
  match n with
  | 0 => some []
  | n + 1 =>
  match L with
  | [] => some (List.replicate (n + 1) 0)
  | A :: L =>
  match dimension A with
  | none => none
  | some D =>
  match L.all (some D = dimension .) with
  | false => none
  | true => some ((A :: L).length :: D)

-- list with length of list down head path at each layer
def head_dimension (L : Hyperlist α n) :=
  match n with
  | 0 => []
  | n + 1 =>
  match L with
  | [] => List.replicate (n + 1) 0
  | A :: L => (A :: L).length :: head_dimension A

-- dimension is well-defined, all lists at each layer have uniform length
def uniform (L : Hyperlist T n) := L.dimension.isSome

-- in a uniform hyperlist
-- computing dimension with checks is the same as computing it down the head
lemma dimension_eq_of_uniform {L : Hyperlist α n} :
    uniform L → dimension L = some (head_dimension L) := by
  unfold uniform; unfold dimension; unfold head_dimension
  cases n <;> dsimp; . intro; rfl
  cases L <;> dsimp; . intro; rfl
  cases h : dimension _ <;> dsimp; . intro; contradiction
  cases List.all _ (some _ = dimension .) <;> dsimp; . intro; contradiction
  simp; apply Option.some_inj.mp; rw[←h]
  apply dimension_eq_of_uniform; unfold uniform; rw[h]; trivial

-- access with list of indices by layer
-- none if length does not match or an index of out-of-bounds
@[simp]
def get? (L : Hyperlist α n) (I : List ℕ) : Option α :=
  match n, I with
  | 0, [] => some L
  | _ + 1, i :: I => (Option.map (get? . I) (List.get? L i)).getD none
  | _, _ => none

-- if access works, then index list length is hyperlist dimension
lemma length_eq_of_get_some {L : Hyperlist α n} :
    (get? L I).isSome → I.length = n := by
  unfold Option.isSome; unfold get?
  cases n; . intro; cases I; rfl; contradiction
  cases I <;> dsimp; . intro; contradiction
  cases List.get? L _ <;> dsimp; . intro; contradiction
  cases h : get? _ _ <;> dsimp; . intro; contradiction
  simp
  apply length_eq_of_get_some; rw[h]; trivial

end Hyperlist

section Merge

@[simp]
def List.merge_nodups
  [LinearOrder α]
  (is1 is2 : List α) :
  List α :=
  match is1, is2 with
  | [], is2 => is2
  | is1, [] => is1
  | i1 :: is1, i2 :: is2 =>
  match compare i1 i2 with
  | .lt => i1 :: merge_nodups is1 (i2 :: is2)
  | .gt => i2 :: merge_nodups (i1 :: is1) is2
  | .eq => i1 :: merge_nodups is1 is2

lemma List.merge_comm [LinearOrder α] {as1 as2 : List α} : merge_nodups as1 as2 = merge_nodups as2 as1 := by sorry
lemma List.merge_nil [LinearOrder α] {as : List α} : merge_nodups [] as = as := by simp
lemma List.merge_nil' [LinearOrder α] {as : List α} : merge_nodups as [] = as := by rw[merge_comm]; simp

@[simp]
def List.zipWith_zeros
    [Zero α] [Zero β]
    (f : α → β → γ)
    (as : List α) (bs : List β) :
    List γ :=
  let aL := as.length
  let bL := bs.length
  let as := as ++ replicate (max aL bL - aL) 0
  let bs := bs ++ replicate (max aL bL - bL) 0
  zipWith f as bs

@[simp]
def Hyperlist.merge_nodups_for_zipWith_zeros
    [LinearOrder σ] [Zero α] [Zero β]
    (is1 is2 : List σ)
    (f : α → β → γ)
    (as : Hyperlist α is1.length) (bs : Hyperlist β is2.length) :
    Hyperlist γ (List.merge_nodups is1 is2).length := by
  match is1, is2 with
  | [], [] => simp; exact f as bs
  | [], i2 :: is2 =>
    match bs with
    | [] => rw[List.merge_nil]; exact hlc []
    | b :: bs => rw[List.merge_nil]; apply hlc'; exact (by rw[←@List.merge_nil _ _ is2]; exact merge_nodups_for_zipWith_zeros [] is2 f as b) :: Hyperlist.map (f 0) (hlc bs)
  | i1 :: is1, [] =>
    match as with
    | [] => rw[List.merge_nil']; exact hlc []
    | a :: as => rw[List.merge_nil']; apply hlc'; exact (by rw[←@List.merge_nil' _ _ is1]; exact merge_nodups_for_zipWith_zeros is1 [] f a bs) :: Hyperlist.map (fun x => f x 0) (hlc as)
  | i1 :: is1, i2 :: is2 =>
  match h1 : as.length, h2 : bs.length with
  | none, _ => contradiction
  | _, none => contradiction
  | some aL, some bL =>
  match h : compare i1 i2 with
  | .lt =>
    unfold List.merge_nodups; rw[h]
    exact List.map (merge_nodups_for_zipWith_zeros is1 (i2 :: is2) f . bs) as
  | .gt =>
    unfold List.merge_nodups; rw[h]
    exact List.map (merge_nodups_for_zipWith_zeros (i1 :: is1) is2 f as .) bs
  | .eq =>
    unfold List.merge_nodups; rw[h]
    exact List.zipWith_zeros (merge_nodups_for_zipWith_zeros is1 is2 f . .) as bs

@[simp]
noncomputable def Hyperlist.expand [Semiring γ] (C : R → γ) (X : σ → γ) :
  (is : List σ) → (cs : Hyperlist R is.length) →
  (n : Option ℕ) → cs.length = n → γ
| [], cs, _, _ => C cs
| i :: is, [], _, _ => 0
| i :: is, c :: cs, none, _ => by contradiction
| i :: is, c :: cs, some n, h =>
  expand C X (i :: is) cs (some n.pred) (
    Option.some_inj.mpr (
      Nat.pred_eq_of_eq_succ (Option.some_inj.mp h).symm ).symm ) +
  X i ^ n.pred * expand C X is c c.length rfl
termination_by is cs => (is.length, cs.length)
decreasing_by
. apply Prod.Lex.right; apply lt_add_one
. apply Prod.Lex.left; simp

end Merge

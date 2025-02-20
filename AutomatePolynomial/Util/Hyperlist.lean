import Mathlib.Data.List.Defs

-- n-dimensional list structure
def Hyperlist (α : Type*) (n : ℕ) :=
  match n with
  | 0 => α
  | n + 1 => List (Hyperlist α n)

-- list of nats bounded from above
def Finlist (D : List ℕ) :=
  { L : List ℕ //
    L.length = D.length ∧ (List.zip L D).all (fun (n, d) => n < d) }

namespace Hyperlist

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
theorem dimension_eq_of_uniform {L : Hyperlist α n} :
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
def get? (L : Hyperlist α n) (I : List ℕ) : Option α := by
  rw[show α = Hyperlist α 0 by rfl]; exact (
  match n, I with
  | 0, [] => some L
  | _ + 1, i :: I => ((List.get? L i).map (get? . I)).getD none
  | _, _ => none )

-- if access works, then index list length is hyperlist dimension
theorem length_eq_of_get_some {L : Hyperlist α n} :
    (get? L I).isSome → I.length = n := by
  unfold Option.isSome; unfold get?
  cases n; . intro; cases I; rfl; contradiction
  cases I <;> dsimp; . intro; contradiction
  cases List.get? L _ <;> dsimp; . intro; contradiction
  cases h : get? _ _ <;> dsimp; . intro; contradiction
  simp
  apply length_eq_of_get_some; rw[h]; trivial

end Hyperlist

-- a uniform hyperlist
def Cubelist (α : Type*) (n : Nat) :=
  { L : Hyperlist α n // L.uniform }

-- because of dimension_eq_of_uniform, head_dimension works
def Cubelist.dimension (L : Cubelist α n) := L.val.head_dimension

-- a hyperlist of specified dimension
def Cubevector (α : Type*) (D : List ℕ) :=
  { L : Hyperlist α D.length // L.dimension = some D }

-- because of dimension_eq_of_uniform, head_dimension works
def Cubevector.dimension (L : Cubevector α D) := L.val.head_dimension

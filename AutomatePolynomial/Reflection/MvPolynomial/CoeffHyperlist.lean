import AutomatePolynomial.Reflection.MvPolynomial.VarList

namespace MvPolynomial

variable (R : Type*) [CommSemiring R]
variable (σ : Type*) [LinearOrder σ]

abbrev MvCoeffsHyperlistType := fun (_ : MvVarsLeListType σ) => Hyperlist R
abbrev MvVoeffsHyperlistTransform : (V : MvVarsLeListType σ) → MvCoeffsHyperlistType R σ V → (σ →₀ ℕ) → R := fun ⟨I, _⟩ C m => (C.get? (I.map m)).getD 0
abbrev MvCoeffsHyperlist (p : MvPolynomial σ R) := MvCoeffs (MvVarsLeListType σ) (MvCoeffsHyperlistType R σ) (MvVarsLeListTransform σ) (MvVoeffsHyperlistTransform R σ) p

noncomputable instance instMvCoeffsReflection : MvCoeffsReflection R (MvVarsLeListType σ) (MvCoeffsHyperlistType R σ) (MvVarsLeListTransform σ) (MvVoeffsHyperlistTransform R σ) where

  mk_zero := {
    V := sorry
    C := sorry
    isLe := sorry
    isEq := sorry }

  mk_C _ := {
    V := sorry
    C := sorry
    isLe := sorry
    isEq := sorry }

  mk_X i := {
    V := sorry
    C := sorry
    isLe := sorry
    isEq := sorry }

  mk_XPow i n := {
    V := sorry
    C := sorry
    isLe := sorry
    isEq := sorry }

  mk_pow _ n P := {
    V := sorry
    C := sorry
    isLe := sorry
    isEq := sorry }

  mk_mul _ _ P Q := {
    V := sorry
    C := sorry
    isLe := sorry
    isEq := sorry }

  mk_add _ _ P Q := {
    V := sorry
    C := sorry
    isLe := sorry
    isEq := sorry }

end MvPolynomial

/-
namespace MvPolynomial

variable [CommSemiring R] [LinearOrder σ]

-- compute polynomial coefficients
class MvCoeffs (p : MvPolynomial σ R) where
  I : List σ
  C : Hyperlist R
  isSorted : I.Pairwise (. < .)
  isSupported : p.vars ⊆ ⟨I, List.Pairwise.imp ne_of_lt isSorted⟩
  isEqAt : ∀ m, p.coeff m = (C.get? (I.map m)).getD 0

namespace MvCoeffs

-- see expandAux spec
@[simp]
noncomputable def expand (p : MvPolynomial σ R) [MvCoeffs p] : { q // p = q } :=
  ⟨ expandAux (MvCoeffs.I p) (MvCoeffs.C p) 0, sorry ⟩

end MvCoeffs

section MvCoeffs

-- the zero polynomial has coefficients 0
@[simp]
instance instMvCoeffsZero : MvCoeffs (0 : MvPolynomial σ R) where
  I := []
  C := ⟨0, .nil⟩
  isSorted := by simp
  isSupported := by trivial
  isEqAt := by intro; rfl

-- the one polynomial has coefficient 1 at degree 0
@[simp]
instance instMvCoeffsOne : MvCoeffs (1 : MvPolynomial σ R) where
  I := []
  C := ⟨1, .nil⟩
  isSorted := by simp
  isSupported := sorry
  isEqAt := sorry

-- the constant c polynomial has coefficient c at degree 0
@[simp]
instance instMvCoeffsC : MvCoeffs (C c : MvPolynomial σ R) where
  I := []
  C := ⟨c, .nil⟩
  isSorted := by simp
  isSupported := sorry
  isEqAt := sorry

-- the identity polynomial has coefficient 1 at degree 1
@[simp]
instance instMvCoeffsX : MvCoeffs (X i : MvPolynomial σ R) where
  I := [i]
  C := ⟨0, .node 1 .nil .nil⟩
  isSorted := by simp
  isSupported := sorry
  isEqAt := sorry

-- compute coefficients of sum
variable (p q : MvPolynomial σ R) [MvCoeffs p] [MvCoeffs q]
@[simp]
instance instMvCoeffAdd : MvCoeffs (p + q) where
  I := List.merge_nodups (MvCoeffs.I p) (MvCoeffs.I q)
  C := MvCoeffs.addAux (MvCoeffs.I p) (MvCoeffs.I q) (MvCoeffs.C p) (MvCoeffs.C q)
  isSorted := sorry
  isSupported := sorry
  isEqAt := sorry

end MvCoeffs

end MvPolynomial
-/

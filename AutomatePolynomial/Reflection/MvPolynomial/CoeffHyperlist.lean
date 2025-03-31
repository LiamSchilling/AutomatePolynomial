import AutomatePolynomial.Reflection.MvPolynomial.VarList

namespace MvPolynomial

variable [LinearOrder σ]
variable [CommSemiring R]

abbrev MvCoeffsHyperlistType (p : MvPolynomial σ R) := MvVarsLeList p × Hyperlist R
@[simp] abbrev MvCoeffsHyperlistTransform (p : MvPolynomial σ R) : MvCoeffsHyperlistType p → (σ →₀ ℕ) → R := fun ⟨⟨⟨I, _⟩, _⟩, C⟩ m => (C.get? (I.map m)).getD 0
abbrev MvCoeffsHyperlist (p : MvPolynomial σ R) := MvCoeffs MvCoeffsHyperlistType MvCoeffsHyperlistTransform p

noncomputable instance instMvCoeffsReflection : MvCoeffsNormalReflection σ R MvCoeffsHyperlistType MvCoeffsHyperlistTransform where

  mk_zero := {
    C := ⟨instMvVarsLeListReflection.mk_zero, ⟨0, .nil⟩⟩
    isEq := sorry }

  mk_C c := {
    C := ⟨instMvVarsLeListReflection.mk_C c, ⟨c, .nil⟩⟩
    isEq := sorry }

  mk_X i := {
    C := ⟨instMvVarsLeListReflection.mk_X i, ⟨0, .node 1 .nil .nil⟩⟩
    isEq := sorry }

  mk_XPow i n := {
    C := ⟨instMvVarsLeListReflection.mk_XPow i n, sorry⟩
    isEq := sorry }

  mk_pow _ n P := {
    C := ⟨instMvVarsLeListReflection.mk_pow _ n P.C.fst, sorry⟩
    isEq := sorry }

  mk_mul _ _ P Q := {
    C := ⟨instMvVarsLeListReflection.mk_mul _ _ P.C.fst Q.C.fst, sorry⟩
    isEq := sorry }

  mk_add _ _ P Q := {
    C := ⟨instMvVarsLeListReflection.mk_add _ _ P.C.fst Q.C.fst, MvCoeffs.addAux P.C.fst.V.val Q.C.fst.V.val P.C.snd Q.C.snd⟩
    isEq := sorry }

  mk_norm p := {
    Normal := sorry
    normalize T := sorry
    normalize_idempotent := sorry }

  transform T := ⟨
    MvCoeffs.expandAux T.C.fst.V.val T.C.snd 0,
    sorry ⟩

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

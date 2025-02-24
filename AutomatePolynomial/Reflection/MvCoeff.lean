import AutomatePolynomial.Util.MvPolynomial

namespace MvPolynomial

variable [CommSemiring R] [LinearOrder σ]

-- compute polynomial coefficients
class MvCoeffs (p : MvPolynomial σ R) where
  I : List σ
  C : Hyperlist R I.length
  isSorted : I.Pairwise (. < .)
  isSupported : p.vars ⊆ ⟨I, List.Pairwise.imp ne_of_lt isSorted⟩
  isEqAt : ∀ m, p.coeff m = (C.get? (I.map m)).getD 0

-- given coefficients [cn, ... c1, c0]
-- computes abstract polynomial (c0 + c1*x + ... cn*x^n)
@[simp]
noncomputable def MvCoeffs.expand (p : MvPolynomial σ R) [MvCoeffs p] : { q // p = q } :=
  ⟨ Hyperlist.expand MvPolynomial.C X (MvCoeffs.I p) (MvCoeffs.C).reverse (MvCoeffs.C).reverse.length rfl, sorry ⟩

section MvCoeffs

@[simp]
instance instMvCoeffsZero : MvCoeffs (0 : MvPolynomial σ R) where
  I := []
  C := hl0 0
  isSorted := by simp
  isSupported := by trivial
  isEqAt := by intro; rfl

@[simp]
instance instMvCoeffsOne : MvCoeffs (1 : MvPolynomial σ R) where
  I := []
  C := hl0 1
  isSorted := by simp
  isSupported := sorry
  isEqAt := sorry

@[simp]
instance instMvCoeffsC : MvCoeffs (C c : MvPolynomial σ R) where
  I := []
  C := hl0 c
  isSorted := by simp
  isSupported := sorry
  isEqAt := sorry

@[simp]
instance instMvCoeffsX : MvCoeffs (X i : MvPolynomial σ R) where
  I := [i]
  C := [ hl0 0, hl0 1 ]
  isSorted := by simp
  isSupported := sorry
  isEqAt := sorry

variable (p q : MvPolynomial σ R) [P : MvCoeffs p] [Q : MvCoeffs q]
@[simp]
instance instMvCoeffAdd : MvCoeffs (p + q : MvPolynomial σ R) where
  I := List.merge_nodups P.I Q.I
  C := Hyperlist.merge_nodups_for_zipWith_zeros P.I Q.I (. + .) P.C.reverse Q.C.reverse
  isSorted := sorry
  isSupported := sorry
  isEqAt := sorry

end MvCoeffs

end MvPolynomial

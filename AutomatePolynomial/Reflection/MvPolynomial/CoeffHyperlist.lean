import AutomatePolynomial.Reflection.MvPolynomial.VarList
import AutomatePolynomial.Representation.MvPolynomial.CoeffHyperlist

/-!
# *Implementation*: Coefficient Hyperlists

 -/

namespace MvPolynomial.Rfl

open CoeffHyperlist

variable [LinearOrder σ] [CommSemiring R]

/- The underlying data for a hyperlist representation of polynomial coefficients -/
abbrev MvCoeffsHyperlistType (p : MvPolynomial σ R) :=
  MvVarsList p × Hyperlist R

/- Transform the underlying data for a hyperlist representation of polynomial coefficients
to the function it represents -/
@[simp]
abbrev MvCoeffsHyperlistRep (p : MvPolynomial σ R) : MvCoeffsHyperlistType p → (σ →₀ ℕ) → R :=
  fun ⟨⟨⟨I, _⟩, _⟩, C⟩ m => (C.getElem? (I.map m)).getD 0

/- A hyperlist representation of polynomial coefficients -/
abbrev MvCoeffsHyperlist (p : MvPolynomial σ R) :=
  MvCoeffs MvCoeffsHyperlistType MvCoeffsHyperlistRep p

/- A reflection system for `MvCoeffs` using the `MvCoeffsHyperlist` representation -/
noncomputable instance instMvCoeffsHypelistReflection :
    MvCoeffsNormalizerReflection σ R MvCoeffsHyperlistType MvCoeffsHyperlistRep where

  mk_zero := {
    C := ⟨instMvVarsLeListReflection.mk_zero, .list []⟩
    isEq := sorry }

  mk_C c := {
    C := ⟨instMvVarsLeListReflection.mk_C c, .single c⟩
    isEq := sorry }

  mk_X i := {
    C := ⟨instMvVarsLeListReflection.mk_X i, .list [.single 0, .single 1]⟩
    isEq := sorry }

  mk_XPow i n := {
    C := ⟨instMvVarsLeListReflection.mk_XPow i n, sorry⟩
    isEq := sorry }

  mk_pow n P := {
    C := ⟨instMvVarsLeListReflection.mk_pow n P.C.fst, sorry⟩
    isEq := sorry }

  mk_mul P Q := {
    C := ⟨instMvVarsLeListReflection.mk_mul P.C.fst Q.C.fst, sorry⟩
    isEq := sorry }

  mk_add P Q := {
    C := ⟨instMvVarsLeListReflection.mk_add P.C.fst Q.C.fst, add P.C.fst.V.val Q.C.fst.V.val P.C.snd Q.C.snd⟩
    isEq := sorry }

  mk_normalizer p := {
    Normal := sorry
    normalize T := sorry
    normalize_idem := sorry }

  transform T := ⟨
    expandAux T.C.fst.V.val T.C.snd 0,
    sorry ⟩

end MvPolynomial.Rfl

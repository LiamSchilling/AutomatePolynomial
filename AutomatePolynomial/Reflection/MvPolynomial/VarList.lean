import AutomatePolynomial.Reflection.MvPolynomial.Defs
import AutomatePolynomial.Hyperlist.Lemmas

/-!
# *Implementation*: Variable Lists

 -/

namespace MvPolynomial.Rfl

variable [LinearOrder σ] [CommSemiring R]

/- The underlying data for a list representation of polynomial variables -/
abbrev MvVarsListType (_ : MvPolynomial σ R) :=
  { I : List σ // I.Pairwise (. < .) }

/- Transform the underlying data for a list representation of polynomial variables
to the finite set it represents -/
@[simp]
abbrev MvVarsListRep (p : MvPolynomial σ R) : MvVarsListType p → Finset σ :=
  fun ⟨I, h⟩ => ⟨I, List.Pairwise.imp ne_of_lt h⟩

/- A list representation of polynomial variables -/
abbrev MvVarsList (p : MvPolynomial σ R) :=
  MvVarsLe MvVarsListType MvVarsListRep p

/- A reflection system for `MvVarsLe` using the `MvVarsList` representation -/
instance instMvVarsLeListReflection :
    MvVarsReflection σ R MvVarsListType MvVarsListRep where

  mk_zero := {
    V := ⟨[], List.Pairwise.nil⟩
    isLe := sorry }

  mk_C _ := {
    V := ⟨[], List.Pairwise.nil⟩
    isLe := sorry }

  mk_X i := {
    V := ⟨[i], List.pairwise_singleton (. < .) i⟩
    isLe := sorry }

  mk_XPow i n := {
    V := ⟨[i], List.pairwise_singleton (. < .) i⟩
    isLe := sorry }

  mk_pow n P := {
    V := P.V
    isLe := sorry }

  mk_mul P Q := {
    V := ⟨List.nodupsMerge P.V Q.V, sorry⟩
    isLe := sorry }

  mk_add P Q := {
    V := ⟨List.nodupsMerge P.V Q.V, sorry⟩
    isLe := sorry }

end MvPolynomial.Rfl

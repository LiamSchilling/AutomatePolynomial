import AutomatePolynomial.Reflection.MvPolynomial.Defs
import AutomatePolynomial.Core.MvPolynomial

namespace MvPolynomial

variable [LinearOrder σ]
variable [CommSemiring R]

abbrev MvVarsLeListType (_ : MvPolynomial σ R) := { I : List σ // I.Pairwise (. < .) }
@[simp] abbrev MvVarsLeListTransform (p : MvPolynomial σ R) : MvVarsLeListType p → Finset σ := fun ⟨I, h⟩ => ⟨Multiset.ofList I, List.Pairwise.imp ne_of_lt h⟩
abbrev MvVarsLeList (p : MvPolynomial σ R) := MvVarsLe MvVarsLeListType MvVarsLeListTransform p

instance instMvVarsLeListReflection : MvVarsReflection σ R MvVarsLeListType MvVarsLeListTransform where

  mk_zero := {
    V := ⟨[], List.Pairwise.nil⟩
    isLe := sorry }

  mk_C c := {
    V := ⟨[], List.Pairwise.nil⟩
    isLe := sorry }

  mk_X i := {
    V := ⟨[i], List.pairwise_singleton (. < .) i⟩
    isLe := sorry }

  mk_XPow i n := {
    V := ⟨[i], List.pairwise_singleton (. < .) i⟩
    isLe := sorry }

  mk_pow _ n P := {
    V := P.V
    isLe := sorry }

  mk_mul _ _ P Q := {
    V := ⟨List.merge_nodups P.V Q.V, sorry⟩
    isLe := sorry }

  mk_add _ _ P Q := {
    V := ⟨List.merge_nodups P.V Q.V, sorry⟩
    isLe := sorry }

end MvPolynomial

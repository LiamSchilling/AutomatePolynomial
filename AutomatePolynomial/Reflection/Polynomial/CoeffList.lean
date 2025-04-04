import AutomatePolynomial.Reflection.Polynomial.Defs
import AutomatePolynomial.Core.Polynomial

namespace Polynomial

variable [Semiring R]

abbrev CoeffsList := Coeffs (fun _ => List R) (fun _ C n => List.getD C n 0)

noncomputable instance instCoeffsListReflection : CoeffsNormalReflection R (fun _ => List R) (fun _ C n => List.getD C n 0) where

  mk_zero := {
    C := []
    isEq := sorry }

  mk_C c := {
    C := [c]
    isEq := sorry }

  mk_X := {
    C := [0, 1]
    isEq := sorry }

  mk_XPow N := {
    C := List.replicate N 0 ++ [1]
    isEq := sorry }

  mk_pow _ n P := {
    C := Coeffs.powAux n P.C
    isEq := sorry }

  mk_mul _ _ P Q := {
    C := Coeffs.mulAux P.C Q.C
    isEq := sorry }

  mk_add _ _ P Q := {
    C := Coeffs.addAux P.C Q.C
    isEq := sorry }

  mk_norm p := {
    Normal := { T | match T.C.reverse with | [] => True | c :: _ => 0 ≠ c }
    normalize T := ⟨⟨(T.C.reverse.dropWhile (Eq 0 : R → Prop)).reverse, sorry⟩, sorry⟩
    normalize_idempotent := sorry }

  degreeEq_of_normal := by
    intro _ _ ⟨T, _⟩; exact
    ⟨match T.C with | [] => ⊥ | _ :: cs => cs.length, sorry⟩

  leadingCoeff_of_normal := by
    intro _ _ ⟨T, _⟩; exact
    ⟨match T.C.reverse with | [] => 0 | c :: _ => c, sorry⟩

  transform T := ⟨
    Coeffs.expandAux T.C 0,
    sorry ⟩

end Polynomial

/-
namespace Polynomial

variable [Semiring R]

-- compute polynomial coefficients
class Coeffs (p : R[X]) where
  C : List R
  isEqAt : ∀ n, p.coeff n = C[n]?.getD 0

namespace Coeffs

-- asserts there are no ending zeros
def isMinimal {p : R[X]} (T : Coeffs p) :=
  match T.C.reverse with | [] => True | c :: _ => 0 ≠ c

-- what the degree would be if there were no leading zeros
@[simp]
def repDegree {p : R[X]} (T : Coeffs p) :=
  match T.C with | [] => ⊥ | _ :: cs => cs.length

-- what the leading coefficient would be if there were no leading zeros
@[simp]
def repLeading {p : R[X]} (T : Coeffs p) :=
  match T.C.reverse with | [] => 0 | c :: _ => c

-- see expandAux spec
@[simp]
noncomputable def expand (p : R[X]) [Coeffs p] : { q // p = q } := ⟨
  expandAux (Coeffs.C p) 0,
  by
    apply expandAux_eq
    . intros; contradiction
    . simp; apply Coeffs.isEqAt ⟩

-- drops leading zeros with proof of minimality
variable [DecidablePred (Eq 0 : R → Prop)] in
@[simp]
def to_minimal {p : R[X]} (T : Coeffs p) :
    { T' : Coeffs p // T'.isMinimal } := ⟨
  { C := (T.C.reverse.dropWhile (Eq 0 : R → Prop)).reverse
    isEqAt := sorry },
  sorry ⟩

end Coeffs

section Coeffs

-- the zero polynomial has coefficients 0
@[simp]
instance instCoeffsZero : Coeffs (0 : R[X]) where
  C := []
  isEqAt := fun _ => rfl

-- the one polynomial has coefficient 1 at degree 0
@[simp]
instance instCoeffsOne : Coeffs (1 : R[X]) where
  C := [1]
  isEqAt := by
    intro n
    rw[coeff_one]
    match inferInstanceAs (Decidable (n = 0)) with
    | isFalse h =>
      symm; simp [if_neg h, Option.getD_eq_iff]
      apply Or.inr; assumption
    | isTrue h =>
      rw[if_pos h, h]; rfl

-- the constant c polynomial has coefficient c at degree 0
@[simp]
instance instCoeffsC : Coeffs (C c : R[X]) where
  C := [c]
  isEqAt := by
    intro n
    rw[coeff_C]
    match inferInstanceAs (Decidable (n = 0)) with
    | isFalse h =>
      symm; simp [if_neg h, Option.getD_eq_iff]
      apply Or.inr; assumption
    | isTrue h =>
      rw[if_pos h, h]; rfl

-- the identity polynomial has coefficient 1 at degree 1
@[simp]
instance instCoeffsX : Coeffs (X : R[X]) where
  C := [0, 1]
  isEqAt := by
    intro n
    rw[coeff_X]
    match inferInstanceAs (Decidable (1 = n)) with
    | isFalse h =>
      symm; simp [if_neg h, Option.getD_eq_iff]
      match inferInstanceAs (Decidable (0 = n)) with
      | isFalse h =>
        apply Or.inr
        apply (Nat.two_le_iff n).mpr; constructor <;> (symm; assumption)
      | isTrue h =>
        apply Or.inl
        rw[←h]; rfl
    | isTrue h =>
      rw[if_pos h, ←h]; rfl

-- compute coefficients of power
variable (p : R[X]) [Coeffs p] in
@[simp]
instance instCoeffPow : Coeffs (p ^ n) where
  C := Coeffs.powAux n (Coeffs.C p)
  isEqAt := by
    intro
    sorry

-- compute coefficients of product
variable (p q : R[X]) [Coeffs p] [Coeffs q] in
@[simp]
instance instCoeffMul : Coeffs (p * q) where
  C := Coeffs.mulAux (Coeffs.C p) (Coeffs.C q)
  isEqAt := by
    intro
    rw[coeff_mul]
    rw[Finset.Nat.sum_antidiagonal_eq_sum_range_succ (p.coeff . * q.coeff .)]
    rw[Coeffs.mulAux_eq]
    apply Finset.sum_congr
    . rfl
    . intro k _
      rw[←Coeffs.isEqAt, ←Coeffs.isEqAt]

-- compute coefficients of sum
variable (p q : R[X]) [Coeffs p] [Coeffs q] in
@[simp]
instance instCoeffsAdd : Coeffs (p + q) where
  C := Coeffs.addAux (Coeffs.C p) (Coeffs.C q)
  isEqAt := by
    intro
    rw[Coeffs.addAux_eq]
    rw[←Coeffs.isEqAt, ←Coeffs.isEqAt]
    simp

end Coeffs

end Polynomial
-/

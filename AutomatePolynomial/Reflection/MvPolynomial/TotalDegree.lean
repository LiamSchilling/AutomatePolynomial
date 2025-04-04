import AutomatePolynomial.Reflection.MvPolynomial.Defs

namespace MvPolynomial

variable [CommSemiring R]

instance instMvTotalDegreeLeReflection : MvTotalDegreeLeReflection σ R where

  mk_zero := {
    D := 0
    isLe := sorry }

  mk_C _ := {
    D := 0
    isLe := sorry }

  mk_X j := {
    D := 1
    isLe := sorry }

  mk_XPow j n := {
    D := n
    isLe := sorry }

  mk_pow _ n P := {
    D := n * P.D
    isLe := sorry }

  mk_mul _ _ P Q := {
    D := P.D + Q.D
    isLe := sorry }

  mk_add _ _ P Q := {
    D := max P.D Q.D
    isLe := sorry }

end MvPolynomial

/-
namespace MvPolynomial

variable [CommSemiring R] [Nontrivial R]

-- compute greedy upper bound on polynomial degree
class MvDegreeLe (p : MvPolynomial σ R) (i : σ) where
  D : ℕ
  isLe : p.degreeOf i ≤ D

section DegreeLe

-- the zero polynomial has degree at most ⊥
@[simp]
instance instMvDegreeLeZero : MvDegreeLe (0 : MvPolynomial σ R) i where
  D := 0
  isLe := le_of_eq (degreeOf_zero i)

-- the one polynomial has degree at most 0
@[simp]
instance instMvDegreeLeOne : MvDegreeLe (1 : MvPolynomial σ R) i where
  D := 0
  isLe := sorry

-- a constant polynomial has degree at most 0
@[simp]
instance instMvDegreeLeC : MvDegreeLe (C c : MvPolynomial σ R) i where
  D := 0
  isLe := le_of_eq (degreeOf_C c i)

-- the identity in a different variable has degree at most 0
variable {j i : σ} (h : j ≠ i) in
@[simp]
instance instMvDegreeLeXNe : MvDegreeLe (X j : MvPolynomial σ R) i where
  D := 0
  isLe :=
    have _ := h
    sorry

-- the identity polynomial has degree at most 1
@[simp]
instance instMvDegreeLeXGen : MvDegreeLe (X j : MvPolynomial σ R) i where
  D := 1
  isLe := sorry

-- compute constant polynomial degree
-- given decidability of whether the constant is zero
variable [DecidableEq σ] in
@[simp]
instance instMvDegreeLeX : MvDegreeLe (X j : MvPolynomial σ R) i where
  D := if i = j then 1 else 0
  isLe := sorry

-- compute upper bound of the power of a polynomial
-- given upper bound of the polynomial
variable (p : MvPolynomial σ R) [MvDegreeLe p i] in
@[simp]
instance instMvDegreeLePow : MvDegreeLe (p ^ n) i where
  D := n * MvDegreeLe.D p i
  isLe := sorry

-- compute upper bound of the product of polynomials
-- given the upper bound of the polynomials
variable (p q : MvPolynomial σ R) [MvDegreeLe p i] [MvDegreeLe q i] in
@[simp]
instance instMvDegreeLeMul : MvDegreeLe (p * q) i where
  D := MvDegreeLe.D p i + MvDegreeLe.D q i
  isLe := sorry

-- compute upper bound of the sum of polynomials
-- given the upper bound of the polynomials
variable (p q : MvPolynomial σ R) [MvDegreeLe p i] [MvDegreeLe q i] in
@[simp]
instance instMvDegreeLeAdd : MvDegreeLe (p + q) i where
  D := max (MvDegreeLe.D p i) (MvDegreeLe.D q i)
  isLe := sorry

end DegreeLe

end MvPolynomial
-/

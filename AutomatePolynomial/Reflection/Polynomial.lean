import AutomatePolynomial.Reflection.NormalForm
import AutomatePolynomial.Tactic.InferInstance
import AutomatePolynomial.WithBot.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas

import AutomatePolynomial.Core.Polynomial

namespace Polynomial

variable [Semiring R]

section Classes

-- assert upper bound on degree
class DegreeLe (p : R[X]) where
  D : WithBot ℕ
  isLe : p.degree ≤ D

-- assert exact degree
class DegreeEq (p : R[X]) where
  D : WithBot ℕ
  isEq : p.degree = D

-- assert leading coefficient
class LeadingCoeff (p : R[X]) where
  c : R
  isEq : p.leadingCoeff = c

-- computable representation of polynomial coefficients
class Coeffs (α : Type*) (f : α → ℕ → R) (p : R[X]) where
  C : α
  isEq : p.coeff = f C

-- computable representation of polynomial evaluation
class Eval (α : Type*) (f : α → R → R) (p : R[X]) where
  F : α
  isEq : p.eval = f F

-- helper for Coeffs assertion
lemma Coeffs.isEqAt {p : R[X]} [self : Coeffs α f p] (n : ℕ) :
    p.coeff n = f self.C n :=
  congrFun Coeffs.isEq n

-- helper for Eval assertion
lemma Eval.isEqAt {p : R[X]} [self : Eval α f p] (x : R) :
    p.eval x = f self.F x :=
  congrFun Eval.isEq x

end Classes

-- degree of p is definitely less than degree of q
@[simp]
def degreeLt (p q : R[X]) [DegreeLe p] [DegreeEq q] :=
  DegreeLe.D p < DegreeEq.D q

-- degree of p is definitely equal to degree of q
@[simp]
def degreeEq (p q : R[X]) [DegreeEq p] [DegreeEq q] :=
  DegreeEq.D p = DegreeEq.D q

-- power of leading coefficient
@[simp]
def leadingCoeffPow (p : R[X]) (n : ℕ) [LeadingCoeff p] :=
  LeadingCoeff.c p ^ n

-- product of leading coefficients
@[simp]
def leadingCoeffMul (p q : R[X]) [LeadingCoeff p] [LeadingCoeff q] :=
  LeadingCoeff.c p * LeadingCoeff.c q

-- sum of leading coefficients
@[simp]
def leadingCoeffAdd (p q : R[X]) [LeadingCoeff p] [LeadingCoeff q] :=
  LeadingCoeff.c p + LeadingCoeff.c q

-- useful meaning of the computable degree comparison
variable {p q : R[X]} [DegreeEq q] [DegreeLe p] in
lemma apply_degreeLt (h : degreeLt p q) : p.degree < q.degree :=
  lt_of_le_of_lt (DegreeLe.isLe) (DegreeEq.isEq.symm.rec h)

-- useful meaning of the computable degree equality
variable {p q : R[X]} [DegreeEq p] [DegreeEq q] in
lemma apply_degreeEq (h : degreeEq p q) : p.degree = q.degree :=
  DegreeEq.isEq.symm.rec (DegreeEq.isEq.symm.rec h)

-- exact degree implies upper bound on degree
@[simp]
def degreeLe_of_degreeEq (p : R[X]) [DegreeEq p] : DegreeLe p where
  D := DegreeEq.D p
  isLe := DegreeEq.isEq.rec (WithBot.le_self (fun _ => le_of_eq rfl))

section Systems

-- normal form for descriptions of polynomials
-- degree and leading coefficient derivations from normal forms
class PolynomialNormalReflection
    (R : Type*) [Semiring R] (T : R[X] → Type*) where

  mk_norm [DecidableEq R] p : Normalizer (T p)

  degreeEq_of_normal [DecidableEq R] : (mk_norm p).Normal → DegreeEq p
  leadingCoeff_of_normal [DecidableEq R] : (mk_norm p).Normal → LeadingCoeff p

variable {T : R[X] → Type*} [PolynomialNormalReflection R T] in
variable [DecidableEq R] in
@[simp]
def degreeEq_of_normal (self : T p) : DegreeEq p :=
  PolynomialNormalReflection.degreeEq_of_normal (
    (PolynomialNormalReflection.mk_norm p).normalize self )

variable {T : R[X] → Type*} [PolynomialNormalReflection R T] in
variable [DecidableEq R] in
@[simp]
def leadingCoeff_of_normal (self : T p) : LeadingCoeff p :=
  PolynomialNormalReflection.leadingCoeff_of_normal (
    (PolynomialNormalReflection.mk_norm p).normalize self )

-- system of polynomial class reflection
-- rules may be sensitive to zero coefficients and thus cancellations
class SensitivePolynomialBaseReflection
    (R : Type*) [Semiring R] (T : R[X] → Type*) where

  mk_zero : T 0
  mk_one_sns [Nontrivial R] : T 1
  mk_C_zero : T (C 0)
  mk_C_nonzero c [NeZero c] : T (C c)
  mk_X_sns [Nontrivial R] : T X
  mk_XPow_sns [Nontrivial R] n : T (X ^ n)

class SensitivePolynomialClosureReflection
    (R : Type*) [Semiring R] (T : R[X] → Type*) where

  mk_pow_sns
      p [LeadingCoeff p] n [NeZero (leadingCoeffPow p n)] :
      T p → T (p ^ n)

  mk_mul_sns
      p q [LeadingCoeff p] [LeadingCoeff q] [NeZero (leadingCoeffMul p q)] :
      T p → T q → T (p * q)

  mk_add_left
      p q [DegreeEq p] [DegreeLe q] (_ : degreeLt q p) :
      T p → T q → T (p + q)

  mk_add_right
      p q [DegreeLe p] [DegreeEq q] (_ : degreeLt p q) :
      T p → T q → T (p + q)

  mk_add_balanced
      p q [DegreeEq p] [DegreeEq q] (_ : degreeEq p q) :
      T p → T q → T (p + q)

-- system of polynomial class reflection
-- rules are independent of zero coefficients
class PolynomialBaseReflection
    (R : Type*) [Semiring R] (T : R[X] → Type*) extends
    SensitivePolynomialBaseReflection R T where

  mk_one : T 1
  mk_C c : T (C c)
  mk_X : T X
  mk_XPow n : T (X ^ n)

  mk_one_sns := mk_one
  mk_C_nonzero c := mk_C c
  mk_X_sns := mk_X
  mk_XPow_sns n := mk_XPow n

class PolynomialClosureReflection
    (R : Type*) [Semiring R] (T : R[X] → Type*) extends
    SensitivePolynomialClosureReflection R T where

  mk_pow p n : T p → T (p ^ n)
  mk_mul p q : T p → T q → T (p * q)
  mk_add p q : T p → T q → T (p + q)

  mk_pow_sns p _ n _ := mk_pow p n
  mk_mul_sns p q _ _ _ := mk_mul p q
  mk_add_left p q _ _ _ := mk_add p q
  mk_add_right p q _ _ _ := mk_add p q
  mk_add_balanced p q _ _ _ := mk_add p q

-- system of polynomial reflection that supports rewriting
class PolynomialFormReflection
    (R : Type*) [Semiring R] (T : R[X] → Type*) where

  transform : T p → { q // p = q }

-- systems of polynomial reflection

class DegreeLeReflection (R : Type*) [Semiring R] extends
    PolynomialBaseReflection R DegreeLe,
    PolynomialClosureReflection R DegreeLe

class DegreeEqReflection (R : Type*) [Semiring R] extends
    SensitivePolynomialBaseReflection R DegreeEq,
    SensitivePolynomialClosureReflection R DegreeEq

class LeadingCoeffReflection (R : Type*) [Semiring R] extends
    PolynomialBaseReflection R LeadingCoeff,
    SensitivePolynomialClosureReflection R LeadingCoeff

class CoeffsReflection (α : Type*) (f : α → ℕ → R) extends
    PolynomialBaseReflection R (Coeffs α f),
    PolynomialClosureReflection R (Coeffs α f),
    PolynomialNormalReflection R (Coeffs α f),
    PolynomialFormReflection R (Coeffs α f)

class EvalReflection (α : Type*) (f : α → R → R) extends
    PolynomialBaseReflection R (Eval α f),
    PolynomialClosureReflection R (Eval α f)

end Systems

-- inference rules

section Instances

variable {T : R[X] → Type*}
variable [SensitivePolynomialBaseReflection R T]
variable [SensitivePolynomialClosureReflection R T]
variable [PolynomialBaseReflection R T]
variable [PolynomialClosureReflection R T]
variable (p q : R[X]) [P : Inhabited (T p)] [Q : Inhabited (T q)]

variable [DegreeEq p] [DegreeLe q] (h : degreeLt q p) in
@[simp]
instance instAddLeft : Inhabited (T (p + q)) :=
  match P, Q with
  | ⟨P⟩, ⟨Q⟩ => ⟨SensitivePolynomialClosureReflection.mk_add_left p q h P Q⟩
variable [DegreeLe p] [DegreeEq q] (h : degreeLt p q) in
@[simp]
instance instAddRight : Inhabited (T (p + q)) :=
  match P, Q with
  | ⟨P⟩, ⟨Q⟩ => ⟨SensitivePolynomialClosureReflection.mk_add_right p q h P Q⟩
variable [DegreeEq p] [DegreeEq q] (h : degreeEq p q) in
@[simp]
instance instAddBalanced : Inhabited (T (p + q)) :=
  match P, Q with
  | ⟨P⟩, ⟨Q⟩ => ⟨SensitivePolynomialClosureReflection.mk_add_balanced p q h P Q⟩
@[simp]
instance instAdd : Inhabited (T (p + q)) :=
  match P, Q with
  | ⟨P⟩, ⟨Q⟩ => ⟨PolynomialClosureReflection.mk_add p q P Q⟩

variable [LeadingCoeff p] [LeadingCoeff q] [NeZero (leadingCoeffMul p q)] in
@[simp]
instance instMulSns : Inhabited (T (p * q)) :=
  match P, Q with
  | ⟨P⟩, ⟨Q⟩ => ⟨SensitivePolynomialClosureReflection.mk_mul_sns p q P Q⟩
@[simp]
instance instMul : Inhabited (T (p * q)) :=
  match P, Q with
  | ⟨P⟩, ⟨Q⟩ => ⟨PolynomialClosureReflection.mk_mul p q P Q⟩

variable [LeadingCoeff p] [NeZero (leadingCoeffPow p n)] in
@[simp]
instance instPowSns : Inhabited (T (p ^ n)) :=
  match P with
  | ⟨P⟩ => ⟨SensitivePolynomialClosureReflection.mk_pow_sns p n P⟩
@[simp]
instance instPow : Inhabited (T (p ^ n)) :=
  match P with
  | ⟨P⟩ => ⟨PolynomialClosureReflection.mk_pow p n P⟩

@[simp]
instance instXPowSns [Nontrivial R] : Inhabited (T (X ^ n)) :=
  ⟨SensitivePolynomialBaseReflection.mk_XPow_sns n⟩
@[simp]
instance instXPow : Inhabited (T (X ^ n)) :=
  ⟨PolynomialBaseReflection.mk_XPow n⟩

@[simp]
instance instXSns [Nontrivial R] : Inhabited (T X) :=
  ⟨SensitivePolynomialBaseReflection.mk_X_sns⟩
@[simp]
instance instX : Inhabited (T X) :=
  ⟨PolynomialBaseReflection.mk_X⟩

@[simp]
instance instCNonzero [NeZero c] : Inhabited (T (C c)) :=
  ⟨SensitivePolynomialBaseReflection.mk_C_nonzero c⟩
@[simp]
instance instC : Inhabited (T (C c)) :=
  ⟨PolynomialBaseReflection.mk_C c⟩
@[simp]
instance instCZero : Inhabited (T (C 0)) :=
  ⟨SensitivePolynomialBaseReflection.mk_C_zero⟩

@[simp]
instance instOneSns [Nontrivial R] : Inhabited (T 1) :=
  ⟨SensitivePolynomialBaseReflection.mk_one_sns⟩
@[simp]
instance instOne : Inhabited (T 1) :=
  ⟨PolynomialBaseReflection.mk_one⟩

@[simp]
instance instZero : Inhabited (T 0) :=
  ⟨SensitivePolynomialBaseReflection.mk_zero⟩

end Instances

end Polynomial

-- tactics to employ reflection system

section Tactics

syntax "poly_reflect_degree_le" : tactic
macro_rules
  | `(tactic| poly_reflect_degree_le) =>
    `(tactic| apply le_trans (@Polynomial.DegreeLe.isLe _ _ _ default); dsimp [Polynomial.DegreeLe.D])

syntax "poly_reflect_degree_eq" : tactic
macro_rules
  | `(tactic| poly_reflect_degree_eq) =>
    `(tactic| apply Eq.trans (@Polynomial.DegreeEq.isEq _ _ _ default); dsimp [Polynomial.DegreeEq.D])
syntax "poly_reflect_degree_eq_trying" "<:>" tactic : tactic
macro_rules
  | `(tactic| poly_reflect_degree_eq_trying <:> $t) =>
    `(tactic| apply Eq.trans (@Polynomial.DegreeEq.isEq _ _ _ (@default _ (by infer_instance_trying <:> $t))); dsimp [Polynomial.DegreeEq.D])
syntax "poly_reflect_degree_eq_trying" : tactic
macro_rules
  | `(tactic| poly_reflect_degree_eq_trying) =>
    `(tactic| poly_reflect_degree_eq_trying <:> ( try_reg ))
syntax "poly_reflect_degree_eq_of_coeffs" "VIA" term : tactic
macro_rules
  | `(tactic| poly_reflect_degree_eq_of_coeffs VIA $f) =>
    `(tactic| apply Eq.trans (@Polynomial.DegreeEq.isEq _ _ _ (Polynomial.degreeEq_of_normal (default : Polynomial.Coeffs _ $f _))); dsimp [Polynomial.DegreeEq.D])

syntax "poly_reflect_leading_coeff" : tactic
macro_rules
  | `(tactic| poly_reflect_leading_coeff) =>
    `(tactic| apply Eq.trans (@Polynomial.LeadingCoeff.isEq _ _ _ default); dsimp [Polynomial.LeadingCoeff.c])
syntax "poly_reflect_leading_coeff_trying" "<:>" tactic : tactic
macro_rules
  | `(tactic| poly_reflect_leading_coeff_trying <:> $t) =>
    `(tactic| apply Eq.trans (@Polynomial.LeadingCoeff.isEq _ _ _ (@default _ (by infer_instance_trying <:> $t))); dsimp [Polynomial.LeadingCoeff.c])
syntax "poly_reflect_leading_coeff_trying" : tactic
macro_rules
  | `(tactic| poly_reflect_leading_coeff_trying) =>
    `(tactic| poly_reflect_leading_coeff_trying <:> ( try_reg ))
syntax "poly_reflect_leading_coeff_of_coeffs" "VIA" term : tactic
macro_rules
  | `(tactic| poly_reflect_leading_coeff_of_coeffs VIA $f) =>
    `(tactic| apply Eq.trans (@Polynomial.LeadingCoeff.isEq _ _ _ (Polynomial.leadingCoeff_of_normal (default : Polynomial.Coeffs _ $f _))); dsimp [Polynomial.LeadingCoeff.c])

syntax "poly_reflect_coeff" "VIA" term : tactic
macro_rules
  | `(tactic| poly_reflect_coeff VIA $f) =>
    `(tactic| apply Eq.trans (@Polynomial.Coeffs.isEqAt _ _ _ _ _ (default : Polynomial.Coeffs _ $f _) _); simp [Polynomial.Coeffs.C])
syntax "poly_reflect_eval" "VIA" term : tactic
macro_rules
  | `(tactic| poly_reflect_eval VIA $f) =>
    `(tactic| apply Eq.trans (@Polynomial.Eval.isEqAt _ _ _ _ _ (default : Polynomial.Eval _ $f _) _); simp [Polynomial.Eval.F])
syntax "poly_reflect_expand" "VIA" term : tactic
macro_rules
  | `(tactic| poly_reflect_expand VIA $f) =>
    `(tactic| apply Eq.trans (Polynomial.PolynomialFormReflection.transform (default : Polynomial.Coeffs _ $f _)).property; simp [Polynomial.Coeffs.C, Polynomial.PolynomialFormReflection.transform])

end Tactics










-- SAMPLE

open Polynomial
variable [Semiring R]

instance instDegreeEqReflection : DegreeEqReflection R where

  mk_zero := ⟨⊥, sorry⟩

  mk_one_sns := ⟨0, sorry⟩

  mk_C_zero := ⟨⊥, sorry⟩

  mk_C_nonzero c := ⟨0, sorry⟩

  mk_X_sns := ⟨1, sorry⟩

  mk_XPow_sns n := ⟨n, sorry⟩

  mk_pow_sns p _ n _ P := ⟨n • P.D, sorry⟩

  mk_mul_sns p q _ _ _ P Q := ⟨P.D + P.D, sorry⟩

  mk_add_left p q _ _ _ P Q := ⟨P.D, sorry⟩

  mk_add_right p q _ _ _ P Q := ⟨Q.D, sorry⟩

  mk_add_balanced p q _ _ _ P Q := ⟨P.D, sorry⟩

instance instLeadingCoeffsReflection : LeadingCoeffReflection R where

  mk_zero := ⟨0, sorry⟩

  mk_one := ⟨1, sorry⟩

  mk_C_zero := ⟨0, sorry⟩

  mk_C c := ⟨c, sorry⟩

  mk_X := ⟨1, sorry⟩

  mk_XPow n := ⟨1, sorry⟩

  mk_pow_sns p _ n _ P := ⟨P.c ^ n, sorry⟩

  mk_mul_sns p q _ _ _ P Q := ⟨P.c * Q.c, sorry⟩

  mk_add_left p q _ _ _ P Q := ⟨P.c, sorry⟩

  mk_add_right p q _ _ _ P Q := ⟨Q.c, sorry⟩

  mk_add_balanced p q _ _ _ P Q := ⟨P.c + Q.c, sorry⟩

example : (X ^ 100 : ℤ[X]).degree = 100 := by poly_reflect_degree_eq

example [Nontrivial R] : (C 1 : R[X]).degree = 0 := by poly_reflect_degree_eq
example : (X : R[X]).leadingCoeff = 1 := by poly_reflect_leading_coeff
-- FAILS

instance : LeadingCoeff (1 : R[X]) := @default _ (by infer_instance_trying)
example : NeZero (leadingCoeffPow (1 : ℤ[X]) 2) := by try_reg
example [Nontrivial R] : Inhabited (LeadingCoeff (X * X : ℤ[X])) := by sorry

@[simp]
def f_list (C : List R) (n : ℕ) := C[n]?.getD 0

noncomputable instance instCoeffsReflection_list : CoeffsReflection (List R) f_list where

  mk_zero := ⟨[], sorry⟩

  mk_one := ⟨[1], sorry⟩

  mk_C_zero := ⟨[], sorry⟩

  mk_C c := ⟨[c], sorry⟩

  mk_X := ⟨[0, 1], sorry⟩

  mk_XPow n := ⟨List.replicate n 0 ++ [1], sorry⟩

  mk_pow p n P := ⟨Coeffs.powAux n P.C, sorry⟩

  mk_mul p q P Q := ⟨Coeffs.mulAux P.C Q.C, sorry⟩

  mk_add p q P Q := ⟨Coeffs.addAux P.C Q.C, sorry⟩

  mk_norm p := ⟨
    { T | match T.C.reverse with | [] => True | c :: _ => c ≠ 0 },
    fun T => ⟨⟨(T.C.reverse.dropWhile (Eq 0 : R → Prop)).reverse, sorry⟩, sorry⟩,
    sorry ⟩

  degreeEq_of_normal := by intro _ _ ⟨T, _⟩; exact ⟨
    match T.C.reverse with | [] => ⊥ | _ :: cs => cs.length,
    sorry ⟩

  leadingCoeff_of_normal := by intro _ _ ⟨T, _⟩; exact ⟨
    match T.C.reverse with | [] => 0 | c :: _ => c,
    sorry ⟩

  transform T := ⟨Coeffs.expandAux T.C 0, sorry⟩

example : ((C 2 * X) ^ 2 : ℤ[X]) = C 4 * X ^ 2 := by poly_reflect_expand VIA f_list; unfold_expand_aux; simp

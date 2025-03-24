import AutomatePolynomial.Reflection.NormalForm
import AutomatePolynomial.WithBot.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas

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

lemma DegreeLe.isLeOf {p : R[X]} (self : DegreeLe p) :
    p.degree ≤ self.D :=
  self.isLe

lemma DegreeEq.isEqOf {p : R[X]} (self : DegreeEq p) :
    p.degree = self.D :=
  self.isEq

lemma LeadingCoeff.isEqOf {p : R[X]} (self : LeadingCoeff p) :
    p.leadingCoeff = self.c :=
  self.isEq

lemma Coeffs.isEqOf {p : R[X]} (self : Coeffs α f p) :
    p.coeff = f self.C :=
  self.isEq

lemma Eval.isEqOf {p : R[X]} (self : Eval α f p) :
    p.eval = f self.F :=
  self.isEq

lemma Coeffs.isEqAtOf {p : R[X]} (self : Coeffs α f p) (n : ℕ) :
    p.coeff n = f self.C n :=
  self.isEqAt n

lemma Eval.isEqAtOf {p : R[X]} (self : Eval α f p) (x : R) :
    p.eval x = f self.F x :=
  self.isEqAt x

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

variable (R : Type*) [Semiring R] (T : R[X] → Type*)
variable (α : Type*)

-- normal form for descriptions of polynomials
-- degree and leading coefficient derivations from normal forms
class PolynomialNormalReflection where

  mk_norm [DecidableEq R] p : Normalizer (T p)

  degreeEq_of_normal [DecidableEq R] : (mk_norm p).Normal → DegreeEq p
  leadingCoeff_of_normal [DecidableEq R] : (mk_norm p).Normal → LeadingCoeff p

variable {R : Type*} [Semiring R] in
variable {T : R[X] → Type*} [PolynomialNormalReflection R T] in
variable [DecidableEq R] in
@[simp]
def degreeEq_of_normal (self : T p) : DegreeEq p :=
  PolynomialNormalReflection.degreeEq_of_normal (
    (PolynomialNormalReflection.mk_norm p).normalize self )

variable {R : Type*} [Semiring R] in
variable {T : R[X] → Type*} [PolynomialNormalReflection R T] in
variable [DecidableEq R] in
@[simp]
def leadingCoeff_of_normal (self : T p) : LeadingCoeff p :=
  PolynomialNormalReflection.leadingCoeff_of_normal (
    (PolynomialNormalReflection.mk_norm p).normalize self )

-- system of polynomial class reflection
-- rules may be sensitive to zero coefficients and thus cancellations
class SensitivePolynomialBaseReflection where

  mk_zero : T (C 0)
  mk_C c [NeZero c] : T (C c)
  mk_X [Nontrivial R] : T X
  mk_XPow [Nontrivial R] n : T (X ^ n)

class SensitivePolynomialClosureReflection where

  mk_pow
      p [LeadingCoeff p] n [NeZero (leadingCoeffPow p n)] :
      T p → T (p ^ n)

  mk_mul
      p q [LeadingCoeff p] [LeadingCoeff q] [NeZero (leadingCoeffMul p q)] :
      T p → T q → T (p * q)

  mk_add_left
      p q [DegreeEq p] [DegreeLe q] (_ : degreeLt q p) :
      T p → T q → T (p + q)

  mk_add_right
      p q [DegreeLe p] [DegreeEq q] (_ : degreeLt p q) :
      T p → T q → T (p + q)

  mk_add_balanced
      p q [DegreeEq p] [DegreeEq q]
      [LeadingCoeff p] [LeadingCoeff q] [NeZero (leadingCoeffAdd p q)]
      (_ : degreeEq p q) :
      T p → T q → T (p + q)

-- system of polynomial class reflection
-- rules are independent of zero coefficients
class PolynomialBaseReflection where

  mk_zero : T (C 0)
  mk_C c : T (C c)
  mk_X : T X
  mk_XPow n : T (X ^ n)

-- we include this derivation instead of making PBR extend SPBR
-- to keep SPBR instances invisible to PBR inference
-- reducing the size of a PBR search
@[simp]
def sensitive_of_polynomialBaseReflection
    [PBR : PolynomialBaseReflection R T] :
    SensitivePolynomialBaseReflection R T where

  mk_zero := PBR.mk_zero
  mk_C c := PBR.mk_C c
  mk_X := PBR.mk_X
  mk_XPow n := PBR.mk_XPow n

class PolynomialClosureReflection where

  mk_pow p n : T p → T (p ^ n)
  mk_mul p q : T p → T q → T (p * q)
  mk_add p q : T p → T q → T (p + q)

-- we include this derivation instead of making PCR extend SPCR
-- to keep SPCR instances invisible to PCR inference
-- reducing the size of a PCR search
@[simp]
def sensitive_of_polynomialClosureReflection
    [PCR : PolynomialClosureReflection R T] :
    SensitivePolynomialClosureReflection R T where

  mk_pow p _ n _ := PCR.mk_pow p n
  mk_mul p q _ _ _ := PCR.mk_mul p q
  mk_add_left p q _ _ _ := PCR.mk_add p q
  mk_add_right p q _ _ _ := PCR.mk_add p q
  mk_add_balanced p q _ _ _ _ _ _ := PCR.mk_add p q

-- system of polynomial reflection that supports rewriting
class PolynomialFormReflection where

  transform : T p → { q // p = q }

-- systems of polynomial reflection

class DegreeLeReflection extends
    PolynomialBaseReflection R DegreeLe,
    PolynomialClosureReflection R DegreeLe

class DegreeEqReflection extends
    SensitivePolynomialBaseReflection R DegreeEq,
    SensitivePolynomialClosureReflection R DegreeEq

class LeadingCoeffReflection extends
    PolynomialBaseReflection R LeadingCoeff,
    SensitivePolynomialClosureReflection R LeadingCoeff

class CoeffsReflection (f : α → ℕ → R) extends
    PolynomialBaseReflection R (Coeffs α f),
    PolynomialClosureReflection R (Coeffs α f)

class CoeffsNormalReflection (f : α → ℕ → R) extends
    CoeffsReflection R α f,
    PolynomialNormalReflection R (Coeffs α f),
    PolynomialFormReflection R (Coeffs α f)

class EvalReflection (f : α → R → R) extends
    PolynomialBaseReflection R (Eval α f),
    PolynomialClosureReflection R (Eval α f)

end Systems

section Instances

variable {T : R[X] → Type*}

-- typeclass wraper for class of polynomials
class PolyClass (T : R[X] → Type*) (p : R[X]) where
  inst : T p

-- inst with explicit instance
@[simp]
def PolyClass.instOf (self : PolyClass T p) := self.inst

-- inst with explicit type
@[simp]
def PolyClass.instAs (T : R[X] → Type*) [self : PolyClass T p] := self.inst

-- inference rules

variable [SensitivePolynomialBaseReflection R T]
variable [SensitivePolynomialClosureReflection R T]
variable [PolynomialBaseReflection R T]
variable [PolynomialClosureReflection R T]
variable (p q : R[X]) [P : PolyClass T p] [Q : PolyClass T q]
variable {c : R} {n : ℕ}

@[simp]
instance instDegreeLeOfPolyClass [PolyClass DegreeLe p] :
    DegreeLe p :=
  PolyClass.inst
@[simp]
instance instDegreeEqOfPolyClass [PolyClass DegreeEq p] :
    DegreeEq p :=
  PolyClass.inst
@[simp]
instance instLeadingCoeffOfPolyClass [PolyClass LeadingCoeff p] :
    LeadingCoeff p :=
  PolyClass.inst
@[simp]
instance instCoeffsOfPolyClass [PolyClass (Coeffs α f) p] :
    Coeffs α f p :=
  PolyClass.inst
@[simp]
instance instEvalOfPolyClass [PolyClass (Eval α f) p] :
    Eval α f p :=
  PolyClass.inst

variable [PolyClass DegreeEq p] [PolyClass DegreeLe q] (h : degreeLt q p) in
@[simp]
instance instAddLeft : PolyClass T (p + q) :=
  ⟨SensitivePolynomialClosureReflection.mk_add_left p q h P.inst Q.inst⟩
variable [PolyClass DegreeLe p] [PolyClass DegreeEq q] (h : degreeLt p q) in
@[simp]
instance instAddRight : PolyClass T (p + q) :=
  ⟨SensitivePolynomialClosureReflection.mk_add_right p q h P.inst Q.inst⟩
variable [PolyClass DegreeEq p] [PolyClass DegreeEq q] in
variable [PolyClass LeadingCoeff p] [PolyClass LeadingCoeff q] in
variable [NeZero (leadingCoeffAdd p q)] in
@[simp]
instance instAddSns : PolyClass T (p + q) :=
  match h : compare (DegreeEq.D p) (DegreeEq.D q) with
  | Ordering.gt => ⟨
    @SensitivePolynomialClosureReflection.mk_add_left
      _ _ _ _ p q
      _ (degreeLe_of_degreeEq q) ((compare_iff _ _).mp h)
      P.inst Q.inst ⟩
  | Ordering.lt => ⟨
    @SensitivePolynomialClosureReflection.mk_add_right
      _ _ _ _ p q
      (degreeLe_of_degreeEq p) _ ((compare_iff _ _).mp h)
      P.inst Q.inst ⟩
  | Ordering.eq => ⟨
    @SensitivePolynomialClosureReflection.mk_add_balanced
      _ _ _ _ p q
      _ _ _ _ _ ((compare_iff _ _).mp h)
      P.inst Q.inst ⟩
@[simp]
instance instAdd : PolyClass T (p + q) :=
  ⟨PolynomialClosureReflection.mk_add p q P.inst Q.inst⟩

variable [PolyClass LeadingCoeff p] [PolyClass LeadingCoeff q] in
variable [NeZero (leadingCoeffMul p q)] in
@[simp]
instance instMulSns : PolyClass T (p * q) :=
  ⟨SensitivePolynomialClosureReflection.mk_mul p q P.inst Q.inst⟩
@[simp]
instance instMul : PolyClass T (p * q) :=
  ⟨PolynomialClosureReflection.mk_mul p q P.inst Q.inst⟩

variable [PolyClass LeadingCoeff p] [NeZero (leadingCoeffPow p n)] in
@[simp]
instance instPowSns : PolyClass T (p ^ n) :=
  ⟨SensitivePolynomialClosureReflection.mk_pow p n P.inst⟩
@[simp]
instance instPow : PolyClass T (p ^ n) :=
  ⟨PolynomialClosureReflection.mk_pow p n P.inst⟩

@[simp]
instance instXPowSns [Nontrivial R] : PolyClass T (X ^ n) :=
  ⟨SensitivePolynomialBaseReflection.mk_XPow n⟩
@[simp]
instance instXPow : PolyClass T (X ^ n) :=
  ⟨PolynomialBaseReflection.mk_XPow n⟩

@[simp]
instance instXSns [Nontrivial R] : PolyClass T X :=
  ⟨SensitivePolynomialBaseReflection.mk_X⟩
@[simp]
instance instX : PolyClass T X :=
  ⟨PolynomialBaseReflection.mk_X⟩

@[simp]
instance instCSns [NeZero c] : PolyClass T (C c) :=
  ⟨SensitivePolynomialBaseReflection.mk_C c⟩
@[simp]
instance instC : PolyClass T (C c) :=
  ⟨PolynomialBaseReflection.mk_C c⟩

@[simp]
instance instZeroSns : PolyClass T (C 0) :=
  ⟨SensitivePolynomialBaseReflection.mk_zero⟩
@[simp]
instance instZero : PolyClass T (C 0) :=
  ⟨PolynomialBaseReflection.mk_zero⟩

end Instances

end Polynomial

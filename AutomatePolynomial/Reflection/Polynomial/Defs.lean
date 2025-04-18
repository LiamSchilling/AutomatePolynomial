import AutomatePolynomial.Representation.Normalizer
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Type-class Reflection for Polynomials

## *Reflection Classes*

## *Signatures*

## *Interfaces*

## *Inference Rules*

 -/

namespace Polynomial.Rfl

variable [Semiring R]

section ReflectionClasses

variable {p q : R[X]}

/-- Asserts upper bound on degree -/
@[ext]
class DegreeLe (p : R[X]) where
  D : WithBot ℕ
  isLe : p.degree ≤ D

/-- Asserts exact degree -/
@[ext]
class DegreeEq (p : R[X]) where
  D : WithBot ℕ
  isEq : p.degree = D

/-- Asserts exact leading coefficient -/
@[ext]
class LeadingCoeff (p : R[X]) where
  c : R
  isEq : p.leadingCoeff = c

/-- Asserts exact coefficients with a generic representation -/
@[ext]
class Coeffs (α : R[X] → Type*) (f : ∀ p, α p → ℕ → R) (p : R[X]) where
  C : α p
  isEq : p.coeff = f p C

/-- Asserts exact evaluation with a generic representation -/
@[ext]
class Eval (α : R[X] → Type*) (f : ∀ p, α p → R → R) (p : R[X]) where
  F : α p
  isEq : p.eval = f p F

/-- Derive upper bound on degree from exact degree -/
@[simp]
def degreeLe_of_degreeEq (p : R[X]) [DegreeEq p] : DegreeLe p where
  D := DegreeEq.D p
  isLe := DegreeEq.isEq.rec le_rfl

@[simp]
def deg (p : R[X]) [T : DegreeEq p] :=
  T.D

@[simp]
def degUp (p : R[X]) [T : DegreeLe p] :=
  T.D

@[simp]
def lead (p : R[X]) [T : LeadingCoeff p] :=
  T.c

/-- From degree inequality with a representative, we derive degree inequality,
which helps automation if the representation is computable -/
theorem apply_deg_lt [DegreeEq p] [DegreeEq q] (h : deg p < deg q) : p.degree < q.degree :=
  DegreeEq.isEq.symm.rec (DegreeEq.isEq.symm.rec h)

/-- From degree equality with a representative, we derive degree equality,
which helps automation if the representation is computable -/
theorem apply_deg_eq [DegreeEq p] [DegreeEq q]  (h : deg p = deg q) : p.degree = q.degree :=
  DegreeEq.isEq.symm.rec (DegreeEq.isEq.symm.rec h)

/-- From degree inequality with a representative, we derive degree inequality,
which helps automation if the representation is computable -/
theorem apply_degUp_lt [DegreeEq q] [DegreeLe p] (h : degUp p < deg q) : p.degree < q.degree :=
  lt_of_le_of_lt (DegreeLe.isLe) (DegreeEq.isEq.symm.rec h)

/-- From non-zero leading coefficient with a representative,
we derive non-zero leading coefficient,
which helps automation if the representation is computable -/
theorem apply_lead_pow [LeadingCoeff p] (h : lead p ^ n ≠ 0) : p.leadingCoeff ^ n ≠ 0 :=
  LeadingCoeff.isEq.symm.rec h

/-- From non-zero leading coefficient with a representative, we derive non-zero leading coefficient,
which helps automation if the representation is computable -/
theorem apply_lead_mul [LeadingCoeff p] [LeadingCoeff q] (h : lead p * lead q ≠ 0) :
    p.leadingCoeff * q.leadingCoeff ≠ 0 :=
  LeadingCoeff.isEq.symm.rec (LeadingCoeff.isEq.symm.rec h)

/-- From non-zero leading coefficient with a representative,
we derive non-zero leading coefficient,
which helps automation if the representation is computable -/
theorem apply_lead_add [LeadingCoeff p] [LeadingCoeff q] (h : lead p + lead q ≠ 0) :
    p.leadingCoeff + q.leadingCoeff ≠ 0 :=
  LeadingCoeff.isEq.symm.rec (LeadingCoeff.isEq.symm.rec h)

lemma Coeffs.isEqAt [self : Coeffs α f p] (n : ℕ) : p.coeff n = f p self.C n :=
  congrFun Coeffs.isEq n

lemma Eval.isEqAt [self : Eval α f p] (x : R) : p.eval x = f p self.F x :=
  congrFun Eval.isEq x

lemma DegreeLe.isLeOf (self : DegreeLe p) : p.degree ≤ self.D :=
  self.isLe

lemma DegreeEq.isEqOf (self : DegreeEq p) : p.degree = self.D :=
  self.isEq

lemma LeadingCoeff.isEqOf (self : LeadingCoeff p) : p.leadingCoeff = self.c :=
  self.isEq

lemma Coeffs.isEqOf (self : Coeffs α f p) : p.coeff = f p self.C :=
  self.isEq

lemma Eval.isEqOf (self : Eval α f p) : p.eval = f p self.F :=
  self.isEq

lemma Coeffs.isEqAtOf (self : Coeffs α f p) (n : ℕ) : p.coeff n = f p self.C n :=
  self.isEqAt n

lemma Eval.isEqAtOf (self : Eval α f p) (x : R) : p.eval x = f p self.F x :=
  self.isEqAt x

end ReflectionClasses

section Signatures

variable (R : Type*) [Semiring R] (T : R[X] → Type*)

/-- Cancellation-sensitive rules for base cases (`0`, `C c`, `X`, `X ^ n`)

Since witnesses of non-zero are necessary for some rules,
more powerful inference tactics must be used to employ this system. -/
class SensitiveBaseReflection where
  mk_zero : T (C 0)
  mk_C c : c ≠ 0 → T (C c)
  mk_X [Nontrivial R] : T X
  mk_XPow [Nontrivial R] n : T (X ^ n)

/-- Cancellation-sensitive rules for recursive cases (`^`, `*`, `+`)

Since witnesses of predicates on `degree` or `leadingCoeff` are necessary for some rules,
more powerful inference tactics must be used to employ this system. -/
class SensitiveClosureReflection where
  mk_pow n : p.leadingCoeff ^ n ≠ 0 → T p → T (p ^ n)
  mk_mul : p.leadingCoeff * q.leadingCoeff ≠ 0 → T p → T q → T (p * q)
  mk_add_left : q.degree < p.degree → T p → T (p + q)
  mk_add_right : p.degree < q.degree → T q → T (p + q)
  mk_add_bal : p.degree = q.degree → p.leadingCoeff + q.leadingCoeff ≠ 0 → T p → T q → T (p + q)

/-- Cancellation-insensitive rules for base cases (`0`, `C c`, `X`, `X ^ n`) -/
class BaseReflection where
  mk_zero : T (C 0)
  mk_C c : T (C c)
  mk_X : T X
  mk_XPow n : T (X ^ n)

/-- Cancellation-insensitive rules for recursive cases (`^`, `*`, `+`) -/
class ClosureReflection where
  mk_pow n : T p → T (p ^ n)
  mk_mul : T p → T q → T (p * q)
  mk_add : T p → T q → T (p + q)

/-- Enforces a normal form on a polynomial representation
and methods to compute exact degree and leading coefficient from normal form -/
class NormalizerReflection where
  mk_normalizer [DecidableEq R] p : Normalizer (T p)
  degreeEq_of_normal [DecidableEq R] : (mk_normalizer p).Normal → DegreeEq p
  leadingCoeff_of_normal [DecidableEq R] : (mk_normalizer p).Normal → LeadingCoeff p

variable {R : Type*} [Semiring R] {T : R[X] → Type*} in
variable [norm : NormalizerReflection R T] [DecidableEq R] in
@[simp]
def degreeEq_use_normal (self : T p) : DegreeEq p :=
  norm.degreeEq_of_normal ((norm.mk_normalizer p).normalize self)

variable {R : Type*} [Semiring R] {T : R[X] → Type*} in
variable [norm : NormalizerReflection R T] [DecidableEq R] in
@[simp]
def leadingCoeff_use_normal (self : T p) : LeadingCoeff p :=
  norm.leadingCoeff_of_normal ((norm.mk_normalizer p).normalize self)

/-- Support for rewriting to a representation-dependent form -/
class FormReflection where
  transform : T p → { q // p = q }

end Signatures

section Interfaces

variable (R : Type*) [Semiring R] (T α : R[X] → Type*)

/-- A reflection system for `DegreeLe` -/
class DegreeLeReflection extends
    BaseReflection R DegreeLe,
    ClosureReflection R DegreeLe

/-- A reflection system for `DegreeEq` -/
class DegreeEqReflection extends
    SensitiveBaseReflection R DegreeEq,
    SensitiveClosureReflection R DegreeEq

/-- A reflection system for `LeadingCoeff` -/
class LeadingCoeffReflection extends
    BaseReflection R LeadingCoeff,
    SensitiveClosureReflection R LeadingCoeff

/-- A reflection system for `Coeffs` -/
class CoeffsReflection (f : ∀ p, α p → ℕ → R) extends
    BaseReflection R (Coeffs α f),
    ClosureReflection R (Coeffs α f)

/-- A reflection system for `Coeffs` with a normal form and rewrite rule -/
class CoeffsNormalizerReflection (f : ∀ p, α p → ℕ → R) extends
    CoeffsReflection R α f,
    NormalizerReflection R (Coeffs α f),
    FormReflection R (Coeffs α f)

/-- A reflection system for `Eval` -/
class EvalReflection (f : ∀ p, α p → R → R) extends
    BaseReflection R (Eval α f),
    ClosureReflection R (Eval α f)

end Interfaces

section InferenceRules

/-- Induces a polynomial class onto a type parameterized over polynomials

Necessary for defining instances with inference arguments,
since a generic type `T` cannot be specified as a class.
Making the polynomial, instead of just the resulting type, a top-level argument of the class
(e.g. `PolyClass T p` instead of `Inhabited (T p)`)
optimizes inference by ensuring that only instances
which could unify with the polynomial are considered. -/
class PolyClass (T : R[X] → Type*) (p : R[X]) where
  inst : T p

@[simp]
def PolyClass.instOf {T : R[X] → Type*} (self : PolyClass T p) :=
  self.inst

@[simp]
def PolyClass.instAs (T : R[X] → Type*) [self : PolyClass T p] :=
  self.inst

variable {T : R[X] → Type*}
variable [SensitiveBaseReflection R T] [SensitiveClosureReflection R T]
variable [BaseReflection R T] [ClosureReflection R T]
variable {p q : R[X]} [P : PolyClass T p] [Q : PolyClass T q]

@[simp]
instance instDegreeLeOfPolyClass [PolyClass DegreeLe p] : DegreeLe p :=
  PolyClass.inst

@[simp]
instance instDegreeEqOfPolyClass [PolyClass DegreeEq p] : DegreeEq p :=
  PolyClass.inst

@[simp]
instance instLeadingCoeffOfPolyClass [PolyClass LeadingCoeff p] : LeadingCoeff p :=
  PolyClass.inst

@[simp]
instance instCoeffsOfPolyClass [PolyClass (Coeffs α f) p] : Coeffs α f p :=
  PolyClass.inst

@[simp]
instance instEvalOfPolyClass [PolyClass (Eval α f) p] : Eval α f p :=
  PolyClass.inst

variable [PolyClass DegreeEq p] [PolyClass DegreeEq q]
variable [PolyClass DegreeLe p] [PolyClass DegreeLe q]
variable [PolyClass LeadingCoeff p] [PolyClass LeadingCoeff q]

@[simp]
instance instAddLeft (h : degUp q < deg p) : PolyClass T (p + q) :=
  ⟨SensitiveClosureReflection.mk_add_left (apply_degUp_lt h) P.inst⟩

@[simp]
instance instAddRight (h : degUp p < deg q) : PolyClass T (p + q) :=
  ⟨SensitiveClosureReflection.mk_add_right (apply_degUp_lt h) Q.inst⟩

@[simp]
instance instAddSns (h : lead p + lead q ≠ 0) : PolyClass T (p + q) :=
  match h' : compare (deg p) (deg q) with
  | Ordering.gt => ⟨
    SensitiveClosureReflection.mk_add_left
      (apply_deg_lt ((compare_iff _ _).mp h')) P.inst ⟩
  | Ordering.lt => ⟨
    SensitiveClosureReflection.mk_add_right
      (apply_deg_lt ((compare_iff _ _).mp h')) Q.inst ⟩
  | Ordering.eq => ⟨
    SensitiveClosureReflection.mk_add_bal
      (apply_deg_eq ((compare_iff _ _).mp h')) (apply_lead_add h) P.inst Q.inst ⟩

@[simp]
instance instAdd : PolyClass T (p + q) :=
  ⟨ClosureReflection.mk_add P.inst Q.inst⟩

@[simp]
instance instMulSns (h : lead p * lead q ≠ 0) : PolyClass T (p * q) :=
  ⟨SensitiveClosureReflection.mk_mul (apply_lead_mul h) P.inst Q.inst⟩

@[simp]
instance instMul : PolyClass T (p * q) :=
  ⟨ClosureReflection.mk_mul P.inst Q.inst⟩

@[simp]
instance instPowSns (h : lead p ^ n ≠ 0) : PolyClass T (p ^ n) :=
  ⟨SensitiveClosureReflection.mk_pow n (apply_lead_pow h) P.inst⟩

@[simp]
instance instPow : PolyClass T (p ^ n) :=
  ⟨ClosureReflection.mk_pow n P.inst⟩

@[simp]
instance instXPowSns [Nontrivial R] : PolyClass T (X ^ n) :=
  ⟨SensitiveBaseReflection.mk_XPow n⟩

@[simp]
instance instXPow : PolyClass T (X ^ n) :=
  ⟨BaseReflection.mk_XPow n⟩

@[simp]
instance instXSns [Nontrivial R] : PolyClass T X :=
  ⟨SensitiveBaseReflection.mk_X⟩

@[simp]
instance instX : PolyClass T X :=
  ⟨BaseReflection.mk_X⟩

@[simp]
instance instCSns [h : NeZero c] : PolyClass T (C c) :=
  ⟨SensitiveBaseReflection.mk_C c h.ne⟩

@[simp]
instance instC : PolyClass T (C c) :=
  ⟨BaseReflection.mk_C c⟩

@[simp]
instance instZeroSns : PolyClass T (C 0) :=
  ⟨SensitiveBaseReflection.mk_zero⟩

@[simp]
instance instZero : PolyClass T (C 0) :=
  ⟨BaseReflection.mk_zero⟩

end InferenceRules

end Polynomial.Rfl

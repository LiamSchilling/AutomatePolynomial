import AutomatePolynomial.Representation.Normalizer
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Typeclass Reflection for Multivariate Polynomials

## *Reflection Classes*

## *Signatures*

## *Interfaces*

## *Inference Rules*

 -/

namespace MvPolynomial.Rfl

variable [CommSemiring R]
variable [AddCommMonoid M] [SemilatticeSup M] [OrderBot M]

section ReflectionClasses

variable {w : σ → M} {p q : MvPolynomial σ R}

/-- Asserts upper bound on the variable set -/
class MvVarsLe
    (α : MvPolynomial σ R → Type*) (f : ∀ p, α p → Finset σ) (p : MvPolynomial σ R) where
  V : α p
  isLe : p.vars ⊆ f p V

/-- Asserts upper bound on weighted total degree -/
class MvWeightedTotalDegreeLe
    (w : σ → M) (p : MvPolynomial σ R) where
  D : M
  isLe : p.weightedTotalDegree w ≤ D

/-- Asserts exact coefficients with a generic representation -/
class MvCoeffs
    (α : MvPolynomial σ R → Type*) (f : ∀ p, α p → (σ →₀ ℕ) → R) (p : MvPolynomial σ R) where
  C : α p
  isEq : p.coeff = f p C

/-- Asserts exact evaluation with a generic representation -/
class MvEval
    (α : MvPolynomial σ R → Type*) (f : ∀ p, α p → (σ → R) → R) (p : MvPolynomial σ R) where
  F : α p
  isEq : (eval . p) = f p F

lemma MvCoeffs.isEqAt [self : MvCoeffs α f p] (m : σ →₀ ℕ) :
    p.coeff m = f p self.C m :=
  congrFun MvCoeffs.isEq m

lemma MvEval.isEqAt [self : MvEval α f p] (m : σ → R) :
    p.eval m = f p self.F m :=
  self.isEq.rec rfl

lemma MvVarsLe.isLeOf (self : MvVarsLe α f p) : p.vars ⊆ f p self.V :=
  self.isLe

lemma MvWeightedTotalDegreeLe.isLeOf (self : MvWeightedTotalDegreeLe w p) :
    p.weightedTotalDegree w ≤ self.D :=
  self.isLe

lemma MvCoeffs.isEqOf (self : MvCoeffs α f p) :
    p.coeff = f p self.C :=
  self.isEq

lemma MvCoeffs.isEqAtOf (self : MvCoeffs α f p) (m : σ →₀ ℕ) :
    p.coeff m = f p self.C m :=
  self.isEqAt m

lemma MvEval.isEqAtOf (self : MvEval α f p) (m : σ → R) :
    p.eval m = f p self.F m :=
  self.isEqAt m

end ReflectionClasses

section Signatures

variable (σ R : Type*) [CommSemiring R] (T : MvPolynomial σ R → Type*)

/-- Cancellation-insensitive rules for base cases (`0`, `C c`, `X i`, `X i ^ n`) -/
class MvBaseReflection where
  mk_zero : T (C 0)
  mk_C c : T (C c)
  mk_X i : T (X i)
  mk_XPow i n : T (X i ^ n)

/-- Cancellation-insensitive rules for recursive cases (`^`, `*`, `+`) -/
class MvClosureReflection where
  mk_pow n : T p → T (p ^ n)
  mk_mul : T p → T q → T (p * q)
  mk_add : T p → T q → T (p + q)

/-- Enforces a normal form on a polynomial representation -/
class MvNormalizerReflection where
  mk_normalizer [DecidableEq R] p : Normalizer (T p)

/-- Support for rewriting to a representation-dependent form -/
class MvFormReflection where
  transform : T p → { q // p = q }

end Signatures

section Interfaces

variable (σ R : Type*) [CommSemiring R] (T α : MvPolynomial σ R → Type*)

/-- A reflection system for `DegreeLe` -/
class MvVarsReflection (f : ∀ p, α p → Finset σ) extends
    MvBaseReflection σ R (MvVarsLe α f),
    MvClosureReflection σ R (MvVarsLe α f)

/-- A reflection system for `DegreeLe` -/
class MvWeightedTotalDegreeLeReflection (w : σ → M) extends
    MvBaseReflection σ R (MvWeightedTotalDegreeLe w),
    MvClosureReflection σ R (MvWeightedTotalDegreeLe w)

/-- A reflection system for `DegreeLe` -/
class MvCoeffsReflection (f : ∀ p, α p → (σ →₀ ℕ) → R) extends
    MvBaseReflection σ R (MvCoeffs α f),
    MvClosureReflection σ R (MvCoeffs α f)

/-- A reflection system for `DegreeLe` -/
class MvCoeffsNormalizerReflection (f : ∀ p, α p → (σ →₀ ℕ) → R) extends
    MvCoeffsReflection σ R α f,
    MvNormalizerReflection σ R (MvCoeffs α f),
    MvFormReflection σ R (MvCoeffs α f)

/-- A reflection system for `DegreeLe` -/
class MvEvalReflection (f : ∀ p, α p → (σ → R) → R) extends
    MvBaseReflection σ R (MvEval α f),
    MvClosureReflection σ R (MvEval α f)

end Interfaces

section InferenceRules

/-- Induces a polynomial class onto a type parameterized over polynomials

Necessary for defining instances with inference arguments,
since a generic type `T` cannot be specified as a class.
Making the polynomial, instead of just the resulting type, a top-level argument of the class
(e.g. `MvPolyClass T p` instead of `Inhabited (T p)`)
optimizes inference by ensuring that only instances
which could unify with the polynomial are considered. -/
class MvPolyClass (T : MvPolynomial σ R → Type*) (p : MvPolynomial σ R) where
  inst : T p

@[simp]
def MvPolyClass.instOf {T : MvPolynomial σ R → Type*} (self : MvPolyClass T p) :=
  self.inst

@[simp]
def MvPolyClass.instAs (T : MvPolynomial σ R → Type*) [self : MvPolyClass T p] :=
  self.inst

variable {T : MvPolynomial σ R → Type*}
variable [MvBaseReflection σ R T] [MvClosureReflection σ R T]
variable {p q : MvPolynomial σ R} [P : MvPolyClass T p] [Q : MvPolyClass T q]

@[simp]
instance instAdd : MvPolyClass T (p + q) :=
  ⟨MvClosureReflection.mk_add P.inst Q.inst⟩

@[simp]
instance instMul : MvPolyClass T (p * q) :=
  ⟨MvClosureReflection.mk_mul P.inst Q.inst⟩

@[simp]
instance instPow : MvPolyClass T (p ^ n) :=
  ⟨MvClosureReflection.mk_pow n P.inst⟩

@[simp]
instance instXPow : MvPolyClass T (X i ^ n) :=
  ⟨MvBaseReflection.mk_XPow i n⟩

@[simp]
instance instX : MvPolyClass T (X i) :=
  ⟨MvBaseReflection.mk_X i⟩

@[simp]
instance instC : MvPolyClass T (C c) :=
  ⟨MvBaseReflection.mk_C c⟩

@[simp]
instance instZero : MvPolyClass T (C 0) :=
  ⟨MvBaseReflection.mk_zero⟩

end InferenceRules

end MvPolynomial.Rfl

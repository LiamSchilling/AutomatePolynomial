import AutomatePolynomial.Reflection.NormalForm
import AutomatePolynomial.WithBot.Basic
import Mathlib.Algebra.MvPolynomial.Variables

namespace MvPolynomial

variable [CommSemiring R]

section Classes

class MvVarsLe (α : MvPolynomial σ R → Type*) (f : ∀ p, α p → Finset σ) (p : MvPolynomial σ R) where
  V : α p
  isLe : p.vars ⊆ f p V

class MvDegreesLe (α : MvPolynomial σ R → Type*) (f : ∀ p, α p → Multiset σ) (p : MvPolynomial σ R) where
  D : α p
  isLe : p.degrees ⊆ f p D

class MvTotalDegreeLe (p : MvPolynomial σ R) where
  D : ℕ
  isLe : p.totalDegree ≤ D

class MvCoeffs (α : MvPolynomial σ R → Type*) (f : ∀ p, α p → (σ →₀ ℕ) → R) (p : MvPolynomial σ R) where
  C : α p
  isEq : p.coeff = f p C

class MvEval (α : MvPolynomial σ R → Type*) (f : ∀ p, α p → (σ → R) → R) (p : MvPolynomial σ R) where
  F : α p
  isEq : (eval . p) = f p F

-- helper for Coeffs assertion
lemma MvCoeffs.isEqAt {p : MvPolynomial σ R} [self : MvCoeffs α f p] (m : σ →₀ ℕ) :
    p.coeff m = f p self.C m :=
  congrFun MvCoeffs.isEq m

lemma MvEval.isEqAt {p : MvPolynomial σ R} [self : MvEval α f p] (m : σ → R) :
    p.eval m = f p self.F m :=
  sorry

lemma MvVarsLe.isLeOf {p : MvPolynomial σ R} (self : MvVarsLe α f p) :
    p.vars ⊆ f p self.V :=
  self.isLe

lemma MvDegreesLe.isLeOf {p : MvPolynomial σ R} (self : MvDegreesLe α f p) :
    p.degrees ⊆ f p self.D :=
  self.isLe

lemma MvTotalDegreeLe.isLeOf {p : MvPolynomial σ R} (self : MvTotalDegreeLe p) :
    p.totalDegree ≤ self.D :=
  self.isLe

lemma MvCoeffs.isEqOf {p : MvPolynomial σ R} (self : MvCoeffs α f p) :
    p.coeff = f p self.C :=
  self.isEq

lemma MvCoeffs.isEqAtOf {p : MvPolynomial σ R} (self : MvCoeffs α f p) (m : σ →₀ ℕ) :
    p.coeff m = f p self.C m :=
  self.isEqAt m

lemma MvEval.isEqAtOf {p : MvPolynomial σ R} (self : MvEval α f p) (m : σ → R) :
    p.eval m = f p self.F m :=
  self.isEqAt m

end Classes

section Systems

variable (σ : Type*)
variable (R : Type*) [CommSemiring R]
variable (T : MvPolynomial σ R → Type*)
variable (α : MvPolynomial σ R → Type*)

class MvPolynomialNormalReflection where

  mk_norm [DecidableEq R] p : Normalizer (T p)

class MvPolynomialBaseReflection where

  mk_zero : T (C 0)
  mk_C c : T (C c)
  mk_X i : T (X i)
  mk_XPow i n : T (X i ^ n)

class MvPolynomialClosureReflection where

  mk_pow p n : T p → T (p ^ n)
  mk_mul p q : T p → T q → T (p * q)
  mk_add p q : T p → T q → T (p + q)

class MvPolynomialFormReflection where

  transform : T p → { q // p = q }

-- systems of polynomial reflection

class MvVarsReflection (f : ∀ p, α p → Finset σ) extends
    MvPolynomialBaseReflection σ R (MvVarsLe α f),
    MvPolynomialClosureReflection σ R (MvVarsLe α f)

class MvDegreesLeReflection (f : ∀ p, α p → Multiset σ) extends
    MvPolynomialBaseReflection σ R (MvDegreesLe α f),
    MvPolynomialClosureReflection σ R (MvDegreesLe α f)

class MvTotalDegreeLeReflection extends
    MvPolynomialBaseReflection σ R MvTotalDegreeLe,
    MvPolynomialClosureReflection σ R MvTotalDegreeLe

class MvCoeffsReflection (f : ∀ p, α p → (σ →₀ ℕ) → R) extends
    MvPolynomialBaseReflection σ R (MvCoeffs α f),
    MvPolynomialClosureReflection σ R (MvCoeffs α f)

class MvCoeffsNormalReflection (f : ∀ p, α p → (σ →₀ ℕ) → R) extends
    MvCoeffsReflection σ R α f,
    MvPolynomialNormalReflection σ R (MvCoeffs α f),
    MvPolynomialFormReflection σ R (MvCoeffs α f)

class MvEvalReflection (f : ∀ p, α p → (σ → R) → R) extends
    MvPolynomialBaseReflection σ R (MvEval α f),
    MvPolynomialClosureReflection σ R (MvEval α f)

end Systems

section Instances

variable {T : MvPolynomial σ R → Type*}

-- typeclass wraper for class of polynomials
class MvPolyClass (T : MvPolynomial σ R → Type*) (p : MvPolynomial σ R) where
  inst : T p

-- inst with explicit instance
@[simp]
def MvPolyClass.instOf (self : MvPolyClass T p) := self.inst

-- inst with explicit type
@[simp]
def MvPolyClass.instAs (T : MvPolynomial σ R → Type*) [self : MvPolyClass T p] := self.inst

-- inference rules

variable [MvPolynomialBaseReflection σ R T]
variable [MvPolynomialClosureReflection σ R T]
variable (p q : MvPolynomial σ R) [P : MvPolyClass T p] [Q : MvPolyClass T q]

@[simp]
instance instAdd : MvPolyClass T (p + q) :=
  ⟨MvPolynomialClosureReflection.mk_add p q P.inst Q.inst⟩

@[simp]
instance instMul : MvPolyClass T (p * q) :=
  ⟨MvPolynomialClosureReflection.mk_mul p q P.inst Q.inst⟩

@[simp]
instance instPow : MvPolyClass T (p ^ n) :=
  ⟨MvPolynomialClosureReflection.mk_pow p n P.inst⟩

@[simp]
instance instXPow : MvPolyClass T (X i ^ n) :=
  ⟨MvPolynomialBaseReflection.mk_XPow i n⟩

@[simp]
instance instX : MvPolyClass T (X i) :=
  ⟨MvPolynomialBaseReflection.mk_X i⟩

@[simp]
instance instC : MvPolyClass T (C c) :=
  ⟨MvPolynomialBaseReflection.mk_C c⟩

@[simp]
instance instZero : MvPolyClass T (C 0) :=
  ⟨MvPolynomialBaseReflection.mk_zero⟩

end Instances

end MvPolynomial

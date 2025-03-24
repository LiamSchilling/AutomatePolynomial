import AutomatePolynomial.Reflection.NormalForm
import AutomatePolynomial.WithBot.Basic
import Mathlib.Algebra.MvPolynomial.Variables

namespace MvPolynomial

variable [CommSemiring R]

section Classes

class MvDegreeLe (i : σ) (p : MvPolynomial σ R) where
  D : ℕ
  isLe : p.degreeOf i ≤ D

class MvVarsLe (α : Type*) (f : α → Finset σ) (p : MvPolynomial σ R) where
  V : α
  isLe : p.vars ⊆ f V

class MvCoeffs (α) (β : α → Type*) (f) (g : (a : α) → β a → (σ →₀ ℕ) → R) (p : MvPolynomial σ R) extends
    MvVarsLe α f p where
  C : β V
  isEq : p.coeff = g V C

-- helper for Coeffs assertion
lemma MvCoeffs.isEqAt {p : MvPolynomial σ R} [self : MvCoeffs α β f g p] (m : σ →₀ ℕ) :
    p.coeff m = g self.V self.C m :=
  congrFun MvCoeffs.isEq m

lemma MvDegreeLe.isLeOf {p : MvPolynomial σ R} (self : MvDegreeLe i p) :
    p.degreeOf i ≤ self.D :=
  self.isLe

lemma MvVarsLe.isLeOf {p : MvPolynomial σ R} (self : MvVarsLe α f p) :
    p.vars ⊆ f self.V :=
  self.isLe

lemma MvCoeffs.isEqOf {p : MvPolynomial σ R} (self : MvCoeffs α β f g p) :
    p.coeff = g self.V self.C :=
  self.isEq

lemma MvCoeffs.isEqAtOf {p : MvPolynomial σ R} (self : MvCoeffs α β f g p) (m : σ →₀ ℕ) :
    p.coeff m = g self.V self.C m :=
  self.isEqAt m

end Classes

section Systems

variable (R : Type*) [CommSemiring R] (T : MvPolynomial σ R → Type*)
variable (α : Type*) (β : α → Type*)

class MvPolynomialNormalReflection where

  mk_norm [DecidableEq R] p : Normalizer (T p)

class MvPolynomialConstantReflection where

  mk_zero : T (C 0)
  mk_C c : T (C c)

class ConstrainedMvPolynomialVariableReflection (i : σ) where

  mk_X : T (X i)
  mk_XNe (_ : i ≠ j) : T (X j)
  mk_XPow n : T (X i ^ n)
  mk_XPowNe n (_ : i ≠ j) : T (X j ^ n)

class MvPolynomialVariableReflection where

  mk_X i : T (X i)
  mk_XPow i n : T (X i ^ n)

class MvPolynomialClosureReflection where

  mk_pow p n : T p → T (p ^ n)
  mk_mul p q : T p → T q → T (p * q)
  mk_add p q : T p → T q → T (p + q)

class MvPolynomialFormReflection where

  transform : T p → { q // p = q }

-- systems of polynomial reflection

class MvDegreeLeReflection (i : σ) extends
    MvPolynomialConstantReflection R (MvDegreeLe i),
    ConstrainedMvPolynomialVariableReflection R (MvDegreeLe i) i,
    MvPolynomialClosureReflection R (MvDegreeLe i)

class MvVarsReflection (f : α → Finset σ) extends
    MvPolynomialConstantReflection R (MvVarsLe α f),
    MvPolynomialVariableReflection R (MvVarsLe α f),
    MvPolynomialClosureReflection R (MvVarsLe α f)

class MvCoeffsReflection (f) (g : (a : α) → β a → (σ →₀ ℕ) → R) extends
    MvPolynomialConstantReflection R (MvCoeffs α β f g),
    MvPolynomialVariableReflection R (MvCoeffs α β f g),
    MvPolynomialClosureReflection R (MvCoeffs α β f g)

class MvCoeffsNormalReflection (f) (g : (a : α) → β a → (σ →₀ ℕ) → R) extends
    MvCoeffsReflection R α β f g,
    MvPolynomialNormalReflection R (MvCoeffs α β f g),
    MvPolynomialFormReflection R (MvCoeffs α β f g)

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

variable [MvPolynomialConstantReflection R T]
variable [ConstrainedMvPolynomialVariableReflection R T i]
variable [MvPolynomialVariableReflection R T]
variable [MvPolynomialClosureReflection R T]
variable (p q : MvPolynomial σ R) [P : MvPolyClass T p] [Q : MvPolyClass T q]

@[simp]
instance instDegreeLeOfPolyClass [MvPolyClass (MvDegreeLe i) p] :
    MvDegreeLe i p :=
  MvPolyClass.inst
@[simp]
instance instVarsOfPolyClass [MvPolyClass (MvVarsLe α f) p] :
    MvVarsLe α f p :=
  MvPolyClass.inst
@[simp]
instance instCoeffsOfPolyClass [MvPolyClass (MvCoeffs α β f g) p] :
    MvCoeffs α β f g p :=
  MvPolyClass.inst

@[simp]
instance instAdd : MvPolyClass T (p + q) :=
  ⟨MvPolynomialClosureReflection.mk_add p q P.inst Q.inst⟩

@[simp]
instance instMul : MvPolyClass T (p * q) :=
  ⟨MvPolynomialClosureReflection.mk_mul p q P.inst Q.inst⟩

@[simp]
instance instPow : MvPolyClass T (p ^ n) :=
  ⟨MvPolynomialClosureReflection.mk_pow p n P.inst⟩

--@[simp]
--instance instXPowNe (h : i ≠ j) : MvPolyClass T (X j ^ n) :=
--  ⟨ConstrainedMvPolynomialVariableReflection.mk_XPowNe n h⟩
@[simp]
instance instXPowCns (_ : True) : MvPolyClass T (X i ^ n) :=
  ⟨ConstrainedMvPolynomialVariableReflection.mk_XPow n⟩
@[simp]
instance instXPow : MvPolyClass T (X i ^ n) :=
  ⟨MvPolynomialVariableReflection.mk_XPow i n⟩

--@[simp]
--instance instXNe (h : i ≠ j) : MvPolyClass T (X j) :=
--  ⟨ConstrainedMvPolynomialVariableReflection.mk_XNe h⟩
@[simp]
instance instXCns (_ : True) : MvPolyClass T (X i) :=
  ⟨ConstrainedMvPolynomialVariableReflection.mk_X⟩
@[simp]
instance instX : MvPolyClass T (X i) :=
  ⟨MvPolynomialVariableReflection.mk_X i⟩

@[simp]
instance instC : MvPolyClass T (C c) :=
  ⟨MvPolynomialConstantReflection.mk_C c⟩

@[simp]
instance instZero : MvPolyClass T (C 0) :=
  ⟨MvPolynomialConstantReflection.mk_zero⟩

end Instances

end MvPolynomial

import AutomatePolynomial.Polynomial
import AutomatePolynomial.WithBot

namespace Polynomial

variable {R : Type*} [Semiring R]
variable [Nontrivial R]
variable [DecidablePred (Eq 0 : R → Prop)]
variable (n : ℕ) (c : R) [NeZero c] (p q : R[X])

-- compute exact polynomial degree
class DegreeEq (p : R[X]) where
  D : WithBot ℕ
  isEq : p.degree = D

-- compute greedy upper bound on polynomial degree
class DegreeLe (p : R[X]) where
  D : WithBot ℕ
  isLe : p.degree ≤ D

-- degree of p is definitely equal to degree of q
@[simp]
def degreeEq [DegreeEq p] [DegreeEq q] :=
  DegreeEq.D p = DegreeEq.D q

-- degree of p is definitely less than degree of q
@[simp]
def degreeLt [DegreeLe p] [DegreeEq q] :=
  DegreeLe.D p < DegreeEq.D q

-- useful meaning of the computable degree equality
omit [Nontrivial R] in
omit [DecidablePred (Eq 0 : R → Prop)] in
variable {p q : R[X]} [DegreeEq p] [DegreeEq q] in
lemma apply_degreeEq (h : degreeEq p q) : p.degree = q.degree :=
  DegreeEq.isEq.symm.rec (DegreeEq.isEq.symm.rec h)

-- useful meaning of the computable degree comparison
omit [Nontrivial R] in
omit [DecidablePred (Eq 0 : R → Prop)] in
variable {p q : R[X]} [DegreeLe p] [DegreeEq q] in
lemma apply_degreeLt (h : degreeLt p q) : p.degree < q.degree :=
  lt_of_le_of_lt (DegreeLe.isLe) (DegreeEq.isEq.symm.rec h)

-- exact degree implies upper bound on degree
def degreeLe_of_degreeEq [DegreeEq p] : DegreeLe p where
  D := DegreeEq.D p
  isLe := DegreeEq.isEq.rec (WithBot.le_self (fun _ => le_of_eq rfl))

section DegreeEq

-- the zero polynomial has degree ⊥
@[simp]
instance instDegreeEqZero : DegreeEq (0 : R[X]) where
  D := ⊥
  isEq := degree_zero

-- the one polynomial over nontrivial types has degree 0
@[simp]
instance instDegreeEqOne : DegreeEq (1 : R[X]) where
  D := 0
  isEq := degree_one

-- the zero constant polynomial has degree ⊥
@[simp]
instance instDegreeEqCZero : DegreeEq (C 0 : R[X]) where
  D := ⊥
  isEq := leadingCoeff_eq_zero_iff_deg_eq_bot.mp (leadingCoeff_C 0)

-- a nonzero constant polynomial has degree 0
@[simp]
instance instDegreeEqCNonzero : DegreeEq (C c : R[X]) where
  D := 0
  isEq := degree_C (NeZero.ne c)

-- compute constant polynomial degree
-- given decidability of whether the constant is zero
@[simp]
instance instDegreeEqC : DegreeEq (C c : R[X]) :=
  match inferInstanceAs (Decidable (0 = c)) with
  | isFalse h => @instDegreeEqCNonzero _ _ _ ⟨fun hn => h hn.symm⟩
  | isTrue h => h.rec instDegreeEqCZero

-- the identity polynomial over nontrivial types has degree 1
@[simp]
instance instDegreeEqX : DegreeEq (X : R[X]) where
  D := 1
  isEq := degree_X

end DegreeEq

section DegreeLe

variable [DegreeLe p] [DegreeLe q]

-- the zero polynomial has degree at most ⊥
@[simp]
instance instDegreeLeZero : DegreeLe (0 : R[X]) :=
  degreeLe_of_degreeEq 0

-- the one polynomial has degree at most 0
@[simp]
instance instDegreeLeOne : DegreeLe (1 : R[X]) where
  D := 0
  isLe := degree_one_le

-- the zero constant polynomial has degree at most ⊥
@[simp]
instance instDegreeLeCZero : DegreeLe (C 0 : R[X]) :=
  degreeLe_of_degreeEq (C 0)

-- a constant polynomial has degree at most 0
@[simp]
instance instDegreeLeC : DegreeLe (C c : R[X]) where
  D := 0
  isLe := degree_C_le

-- the identity polynomial has degree at most 1
@[simp]
instance instDegreeLeX : DegreeLe (X : R[X]) where
  D := 1
  isLe := degree_X_le

-- compute upper bound of the power of a polynomial
-- given upper bound of the polynomial
@[simp]
instance instDegreeLePow : DegreeLe (p ^ n) where
  D := n * DegreeLe.D p
  isLe := degree_pow_le_of_le n DegreeLe.isLe

-- compute upper bound of the product of polynomials
-- given the upper bound of the polynomials
@[simp]
instance instDegreeLeMul : DegreeLe (p * q) where
  D := DegreeLe.D p + DegreeLe.D q
  isLe := degree_mul_le_of_le DegreeLe.isLe DegreeLe.isLe

-- compute upper bound of the sum of polynomials
-- given the upper bound of the polynomials
@[simp]
instance instDegreeLeAdd : DegreeLe (p + q) where
  D := max (DegreeLe.D p) (DegreeLe.D q)
  isLe := degree_add_le_of_le DegreeLe.isLe DegreeLe.isLe

end DegreeLe

end Polynomial

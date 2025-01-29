import Mathlib.Algebra.Polynomial.Degree.Lemmas

-- utility functions for reducing ite
theorem ite_true_eq [Decidable c] (h : c) : ite c a b = a := by
  simp [ show c = True by
    apply propext; apply Iff.intro <;> (intro; trivial) ]
theorem ite_false_eq [Decidable c] (h : ¬c) : ite c a b = b := by
  simp [ show c = False by
    apply propext; apply Iff.intro <;> (intro; contradiction) ]

-- TODO: implement PolynomialSpec.degree
-- TODO: implement PolynomialSpec.add and PolynomialSpec.mul
-- TODO: implement PolynomialTreeSpec.simplify
-- TODO: implement PolynomialTreeSpec.degree_max
-- TODO: show bijectivity of PolynomialSpec.polynomial
-- TODO: show surjectivity of PolynomialTreeSpec.polynomial

-- computable type uniquely specifying polynomials
inductive PolynomialSpec (R : Type*) [Semiring R]
| mk
  : ∀ cs : List R,
    (match cs with | [] => True | c :: _ => c ≠ 0) →
    PolynomialSpec R

-- computable type specifying polynomials
-- computable, constant-time + and *
inductive PolynomialTreeSpec (R : Type*) [Semiring R]
| mk : PolynomialSpec R → PolynomialTreeSpec R
| add : PolynomialTreeSpec R → PolynomialTreeSpec R → PolynomialTreeSpec R
| mul : PolynomialTreeSpec R → PolynomialTreeSpec R → PolynomialTreeSpec R

namespace PolynomialSpec

-- constructs the specifier for the zero polynomial
def zero {R : Type*} [Semiring R] : PolynomialSpec R :=
  mk [] True.intro

-- given coefficients [c0, c1, ... cm] and initial degree n
-- computes abstract polynomial (cm*x^(n+m) + ... c1*x^(n+1) + c0*x^(n))
noncomputable def polynomial_rec
      {R : Type*} [Semiring R]
      (cs : List R) (n : Nat)
      : Polynomial R :=
  match cs with
  | [] => 0
  | c :: cs => polynomial_rec cs n.succ + Polynomial.C c * Polynomial.X ^ n

-- given coefficients [cm, ... c1, c0] in p
-- computes abstract polynomial (cm*x^m + ... c1*x + c0)
noncomputable def polynomial
      {R : Type*} [Semiring R]
      (p : PolynomialSpec R)
      : Polynomial R :=
  match p with
  | ⟨cs, _⟩ => polynomial_rec cs.reverse 0

-- given coefficients [c0, c1, ... cm] and initial degree n
-- computes polynomial function (cm*x^(n+m) + ... c1*x^(n+1) + c0*x^(n))
def function_rec
      {R : Type*} [Semiring R]
      (cs : List R) (n : Nat)
      : R → R :=
  match cs with
  | [] => fun _ => 0
  | c :: cs => fun x => function_rec cs n.succ x + c * x ^ n

-- given coefficients [cm, ... c1, c0] in p
-- computes polynomial function (cm*x^m + ... c1*x + c0)
def function
      {R : Type*} [Semiring R]
      (p : PolynomialSpec R)
      : R → R :=
  match p with
  | ⟨cs, _⟩ => function_rec cs.reverse 0

-- fully unfolds p.polynomial
syntax "unfold_poly_spec" : tactic
macro_rules
| `(tactic| unfold_poly_spec) =>
  `(tactic|
    unfold polynomial; dsimp; repeat unfold polynomial_rec )

-- fully unfolds p.function
syntax "unfold_poly_spec_fun" : tactic
macro_rules
| `(tactic| unfold_poly_spec_fun) =>
  `(tactic|
    unfold function; dsimp; repeat unfold function_rec )

-- shifting coefficients index with access index results in same coefficient
lemma succ_coeff_succ
      {R : Type*} [Semiring R]
      (cs : List R) (n : Nat)
      : ∀ i,
        (polynomial_rec cs n).coeff i =
        (polynomial_rec cs n.succ).coeff i.succ := by
  intro i
  match cs with
  | [] => rfl
  | c :: cs =>
    unfold polynomial_rec
    rw[Polynomial.coeff_add, Polynomial.coeff_add]
    rw[succ_coeff_succ cs n.succ i]
    rw[Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
    rw[Polynomial.coeff_X_pow n i, Polynomial.coeff_X_pow n.succ i.succ]
    simp only [propext Nat.succ_inj]

-- relates elements of (cs) to coefficients of (polynomial_rec cs n)
lemma coeff_eq_getElem
      {R : Type*} [Semiring R]
      (cs : List R) (n : Nat)
      : ∀ i, (polynomial_rec cs n).coeff (i.val + n) = cs.get i := by
  sorry

-- coefficients of (polynomial_rec cs n) at least (cs.length + n) are zero
lemma oob_coeff_eq_zero
      {R : Type*} [Semiring R]
      (cs : List R) (n : Nat)
      : ∀ i, cs.length + n ≤ i → (polynomial_rec cs n).coeff i = 0 := by
  intro i h1
  match cs with
  | [] => rfl
  | c :: cs =>
    rw[List.length_cons, add_comm, ←add_assoc] at h1
    have h2 : i.pred.succ = i :=
      Nat.succ_pred_eq_of_ne_zero (by intro hn; rw[hn] at h1; contradiction)
    have h3 : cs.length + n ≤ i.pred :=
      Nat.le_of_succ_le_succ (by rw[h2, add_comm]; exact h1)
    have h4 : i ≠ n := by
      intro hn; rw[hn] at h1
      absurd le_trans h1 (Nat.le_add_right n cs.length)
      exact Nat.not_succ_le_self (n + cs.length)
    unfold polynomial_rec
    rw[Polynomial.coeff_add]
    nth_rewrite 1 [←h2]
    rw[←succ_coeff_succ cs n i.pred, oob_coeff_eq_zero cs n i.pred h3]
    rw[Polynomial.coeff_C_mul, Polynomial.coeff_X_pow n i]
    rw[ite_false_eq h4]
    simp

-- the degree of the polynomial specified by (c :: cs) is cs.length
lemma cons_degree_eq_length
      {R : Type*} [Semiring R]
      (c : R) (cs : List R) (h1 : c ≠ 0)
      : (mk (c :: cs) h1).polynomial.degree = cs.length := by
  apply Polynomial.degree_eq_of_le_of_coeff_ne_zero
  . apply (Polynomial.degree_le_iff_coeff_zero _ _).mpr
    intro m h2
    apply oob_coeff_eq_zero (c :: cs).reverse 0 m
    rw[List.length_reverse]
    exact WithBot.coe_lt_coe.mp h2
  . have h2 : cs.length < (c :: cs).reverse.length := by
      rw[List.length_reverse]; exact Nat.le_of_eq rfl
    have h3 : (c :: cs).length.pred - cs.length < (c :: cs).length :=
      Nat.sub_lt_succ (c :: cs).length.pred cs.length
    unfold polynomial
    rw[show cs.length = cs.length + 0 by rfl]
    rw[coeff_eq_getElem (c :: cs).reverse 0 ⟨cs.length, h2⟩]
    rw[List.get_reverse' (c :: cs) ⟨cs.length, h2⟩ h3]
    simp
    exact h1

-- computes with proof degree of p.polynomial
def degree
      {R : Type*} [Semiring R]
      (p : PolynomialSpec R)
      : { D : WithBot Nat // p.polynomial.degree = D } :=
  match p with
  | ⟨[], _⟩ => ⟨⊥, rfl⟩
  | ⟨c :: cs, h⟩ => ⟨cs.length, cons_degree_eq_length c cs h⟩

end PolynomialSpec

namespace PolynomialTreeSpec

-- establish + and * typeclasses and ~ prefix for leaf construction
instance {R : Type*} [Semiring R] : Add (PolynomialTreeSpec R) where add := add
instance {R : Type*} [Semiring R] : Mul (PolynomialTreeSpec R) where mul := mul
prefix:75 "~" => mk

-- asserts that p contains only * and ~ constructors, that is no + constructors
def mul_only {R : Type*} [Semiring R] (p : PolynomialTreeSpec R) : Prop :=
  match p with
  | mk _ => True
  | add _ _ => False
  | mul p1 p2 => mul_only p1 ∧ mul_only p2

-- mul_only is decidable by complete traveral
instance dec_mul_only
      {R : Type*} [Semiring R]
      : DecidablePred (mul_only : PolynomialTreeSpec R -> Prop) :=
  fun p =>
  match p with
  | mk _ => isTrue (by trivial)
  | add _ _ => isFalse (by intro; contradiction)
  | mul p1 p2 => @instDecidableAnd _ _ (dec_mul_only p1) (dec_mul_only p2)

-- computes the abstract polynomial specified by p
noncomputable def polynomial
      {R : Type*} [Semiring R]
      (p : PolynomialTreeSpec R)
      : Polynomial R :=
  match p with
  | mk p => p.polynomial
  | add p1 p2 => p1.polynomial + p2.polynomial
  | mul p1 p2 => p1.polynomial * p2.polynomial

-- computes the polynomial function specified by p
def function
      {R : Type*} [Semiring R]
      (p : PolynomialTreeSpec R)
      : R → R :=
  match p with
  | mk p => p.function
  | add p1 p2 => fun x => p1.function x + p2.function x
  | mul p1 p2 => fun x => p1.function x * p2.function x

-- fully unfolds p.polynomial
syntax "unfold_poly_tree_spec" : tactic
macro_rules
| `(tactic| unfold_poly_tree_spec) =>
  `(tactic|
    repeat unfold polynomial; try unfold_poly_spec )

-- fully unfolds p.function
syntax "unfold_poly_tree_spec_fun" : tactic
macro_rules
| `(tactic| unfold_poly_tree_spec_fun) =>
  `(tactic|
    repeat unfold function; try unfold_poly_spec_fun )

-- given that R has no zero divisors and p contains no + constructors
-- computes with proof degree of p.polynomial
def degree_mul_only
      {R : Type*} [Semiring R] [NoZeroDivisors R]
      (p : PolynomialTreeSpec R) (h : mul_only p)
      : { D : WithBot Nat // p.polynomial.degree = D } :=
  match p with
  | mk p => p.degree
  | add _ _ => by contradiction
  | mul p1 p2 =>
    let ⟨D1, h1⟩ := p1.degree_mul_only h.left
    let ⟨D2, h2⟩ := p2.degree_mul_only h.right
    ⟨D1 + D2, by rw [←h1, ←h2]; exact Polynomial.degree_mul⟩

end PolynomialTreeSpec

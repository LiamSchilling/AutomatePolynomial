import AutomatePolynomial.Util.Polynomial

namespace Polynomial

variable [Semiring R]

-- compute polynomial coefficients
class Coeffs (p : R[X]) where
  C : List R
  isEq : p.coeff = fun n => (C.reverse.get? n).getD 0

-- asserts there are no leading zeros
def Coeffs.isMinimal {p : R[X]} (T : Coeffs p) : Prop :=
  match T.C with | [] => True | c :: _ => 0 ≠ c

-- what the degree would be if there were no leading zeros
@[simp]
def Coeffs.repDegree {p : R[X]} (T : Coeffs p) : WithBot ℕ :=
  match T.C with | [] => ⊥ | _ :: cs => cs.length

-- what the leading coefficient would be if there were no leading zeros
@[simp]
def Coeffs.repLeading {p : R[X]} (T : Coeffs p) : R :=
  match T.C with | [] => 0 | c :: _ => c

-- given coefficients [cn, ... c1, c0]
-- computes abstract polynomial (c0 + c1*x + ... cn*x^n)
@[simp]
noncomputable def Coeffs.expand (p : R[X]) [Coeffs p] : { q // p = q } :=
  ⟨ expandAux (Coeffs.C p) (Coeffs.C p).length rfl, sorry ⟩

-- apply equality proof to coefficient at specific degree
lemma Coeffs.isEqAt [Coeffs p] (n : ℕ) :
    p.coeff n = ((Coeffs.C p).reverse.get? n).getD 0 :=
  Coeffs.isEq.symm.rec rfl

-- drops leading zeros with proof of minimality
variable [DecidablePred (Eq 0 : R → Prop)] in
@[simp]
def Coeffs.to_minimal {p : R[X]} (T : Coeffs p) :
    { T' : Coeffs p // T'.isMinimal } := ⟨
  { C := T.C.dropWhile (Eq 0 : R → Prop)
    isEq := sorry },
  sorry ⟩

section Coeffs

-- the zero polynomial has coefficients 0
@[simp]
instance instCoeffsZero : Coeffs (0 : R[X]) where
  C := []
  isEq := sorry

-- the one polynomial has coefficient 1 at degree 0
@[simp]
instance instCoeffsOne : Coeffs (1 : R[X]) where
  C := [1]
  isEq := sorry

-- the constant c polynomial has coefficient c at degree 0
@[simp]
instance instCoeffsC : Coeffs (C c : R[X]) where
  C := [c]
  isEq := sorry

-- the identity polynomial has coefficient 1 at degree 1
@[simp]
instance instCoeffsX : Coeffs (X : R[X]) where
  C := [1, 0]
  isEq := sorry

-- compute coefficients of power
variable (p : R[X]) [Coeffs p] in
@[simp]
instance instCoeffPow : Coeffs (p ^ n) where
  C := Coeffs.powAux n (Coeffs.C p)
  isEq := sorry

-- compute coefficients of product
variable (p q : R[X]) [Coeffs p] [Coeffs q] in
@[simp]
instance instCoeffMul : Coeffs (p * q) where
  C := Coeffs.mulAux (Coeffs.C p) (Coeffs.C q)
  isEq := sorry

-- compute coefficients of sum
variable (p q : R[X]) [Coeffs p] [Coeffs q] in
@[simp]
instance instCoeffsAdd : Coeffs (p + q) where
  C := Coeffs.addAux (Coeffs.C p) (Coeffs.C q)
  isEq := sorry

end Coeffs

end Polynomial

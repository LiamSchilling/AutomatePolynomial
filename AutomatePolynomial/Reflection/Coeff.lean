import AutomatePolynomial.Util.Polynomial

namespace Polynomial

variable {R : Type*} [Semiring R]
variable (n : ℕ) (c : R) (p q : R[X])

-- compute polynomial coefficients
class Coeffs (p : R[X]) where
  N : ℕ
  C : List R
  isLength : C.length = N
  isEq : p.coeff = fun n => (C.reverse.get? n).getD 0

-- apply equality proof to coefficient at specific degree
lemma Coeffs.isEqAt {p : R[X]} [Coeffs p] :
    p.coeff n = ((Coeffs.C p).reverse.get? n).getD 0 :=
  Coeffs.isEq.symm.rec rfl

-- we can append a zero to the front of our coeff list
@[simp]
def coeffs_cons_zero [Coeffs p] : Coeffs p where
  N := Coeffs.N p + 1
  C := 0 :: Coeffs.C p
  isLength := sorry
  isEq := sorry

-- we can append as many zeros as we like
@[simp]
def coeffs_append_zero [Coeffs p] : Coeffs p where
  N := Coeffs.N p + n
  C := List.replicate n 0 ++ Coeffs.C p
  isLength := sorry
  isEq := sorry

section Coeffs

variable [Coeffs p] [Coeffs q]

-- the zero polynomial has coefficients 0
@[simp]
instance instCoeffsZero : Coeffs (0 : R[X]) where
  N := 0
  C := []
  isLength := by simp
  isEq := sorry

-- the one polynomial has coefficient 1 at degree 0
@[simp]
instance instCoeffsOne : Coeffs (1 : R[X]) where
  N := 1
  C := [1]
  isLength := by simp
  isEq := sorry

-- the constant c polynomial has coefficient c at degree 0
@[simp]
instance instCoeffsC : Coeffs (C c : R[X]) where
  N := 1
  C := [c]
  isLength := by simp
  isEq := sorry

-- the identity polynomial has coefficient 1 at degree 1
@[simp]
instance instCoeffsX : Coeffs (X : R[X]) where
  N := 2
  C := [1, 0]
  isLength := by simp
  isEq := sorry

-- compute coefficients of sum given lists have same length
@[simp]
def coeffs_add_balanced (h : Coeffs.N p = Coeffs.N q) : Coeffs (p + q) where
  N := Coeffs.N p
  C := (List.zip (Coeffs.C p) (Coeffs.C q)).map (fun (cp, cq) => cp + cq)
  isLength := sorry
  isEq := sorry

-- compute coefficients of sum
@[simp]
instance instCoeffsAdd : Coeffs (p + q) :=
  @coeffs_add_balanced _ _ _ _
    (coeffs_append_zero (max (Coeffs.N p) (Coeffs.N q) - Coeffs.N p) p)
    (coeffs_append_zero (max (Coeffs.N p) (Coeffs.N q) - Coeffs.N q) q)
    sorry

end Coeffs

end Polynomial

import Mathlib.Algebra.Polynomial.Degree.Lemmas

namespace Polynomial

variable [Semiring R]

@[simp]
def Coeffs.addAux (cs1 cs2 : List R) : List R :=
  let cs1L := cs1.length
  let cs2L := cs2.length
  let cs1 := List.replicate (max cs1L cs2L - cs1L) 0 ++ cs1
  let cs2 := List.replicate (max cs1L cs2L - cs2L) 0 ++ cs2
  (List.zip cs1 cs2).map (fun (c1, c2) => c1 + c2)

@[simp]
def Coeffs.mulConstAux (c : R) (cs : List R) : List R :=
  cs.map (fun c' => c * c')

@[simp]
def Coeffs.mulXPowAux (n : ℕ) (cs : List R) : List R :=
  cs ++ List.replicate n 0

@[simp]
def Coeffs.mulAux (cs1 cs2 : List R) : List R :=
  match cs1 with
  | [] => List.replicate cs2.length.pred 0
  | c :: cs1 => addAux (mulAux cs1 cs2) (mulConstAux c (mulXPowAux cs1.length cs2))

@[simp]
def Coeffs.powAux (n : ℕ) (cs : List R) : List R :=
  match n with
  | 0 => [1]
  | n + 1 => mulAux (powAux n cs) cs

-- given coefficients [cn, ... c1, c0]
-- computes abstract polynomial (c0 + c1*x + ... cn*x^n)
noncomputable def Coeffs.expandAux :
  (cs : List R) →
  (n : ℕ) → cs.length = n → R[X]
| [], _, _ => 0
| c :: cs, n, h =>
  expandAux cs n.pred (
    Nat.pred_eq_of_eq_succ h.symm ).symm +
  C c * X ^ n.pred

end Polynomial

-- fully unfold expand call
syntax "unfold_expand_aux" : tactic
macro_rules
  | `(tactic| unfold_expand_aux) =>
    `(tactic| repeat unfold Polynomial.Coeffs.expandAux)

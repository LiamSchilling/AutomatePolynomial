import AutomatePolynomial.Lemmas

open Polynomial

variable {R : Type*} [Semiring R]

section DegreeEq

-- base cases
example                  : (0 : R[X]).degree = ⊥   := DegreeEq.isEq
example [Nontrivial R]   : (1 : R[X]).degree = 0   := DegreeEq.isEq
example                  : (C 0 : R[X]).degree = ⊥ := DegreeEq.isEq
example [Nontrivial R]   : (C 1 : R[X]).degree = 0 := DegreeEq.isEq
example [NeZero (2 : R)] : (C 2 : R[X]).degree = 0 := DegreeEq.isEq
example [Nontrivial R]   : (X : R[X]).degree = 1   := DegreeEq.isEq

-- closure cases
-- TODO: many of these will depend on reasoning about coefficients,
--       which is not yet well established

end DegreeEq

section DegreeLe

-- base cases
example : (0 : R[X]).degree ≤ ⊥   := DegreeLe.isLe
example : (1 : R[X]).degree ≤ 0   := DegreeLe.isLe
example : (C 0 : R[X]).degree ≤ ⊥ := DegreeLe.isLe
example : (C 1 : R[X]).degree ≤ 0 := DegreeLe.isLe
example : (C 2 : R[X]).degree ≤ 0 := DegreeLe.isLe
example : (X : R[X]).degree ≤ 1   := DegreeLe.isLe

-- closure cases
-- TODO

end DegreeLe

# Automate Polynomial: An Experiment in Reflection for Polynomials

Polynomials are crucial to cryptographic protocols for their error-checking applications. Proof assistants like Lean 4 enable machine-verified implementations of those protocols, yielding more correct and secure systems. While those implementations demand an efficient way to prove properties of polynomials in Lean, representations of polynomials in Lean’s mathematics library are not directly computable, making simple results tedious to prove. To address this issue, we design and implement a general proof-by-reflection model in Lean, reducing mathematical problems to decisions on computable representations. The resulting systems automate proof of degrees, coefficients, evaluations, and expansions for univariate and multivariate polynomials in various contexts.

## The Blueprint

This document will briefly demonstrate the automation capabilities of the our system's tactics and discuss future directions for the project. For a more thorough discussion of previous work, our approach, and how to extend the systems in this project, visit the project's [blueprint](https://liamschilling.github.io/AutomatePolynomial/).

## Demonstrations

The following code samples are adapted from [Demo/Polynomial.lean](https://github.com/LiamSchilling/AutomatePolynomial/tree/master/AutomatePolynomial/Demo/Polynomial.lean) and rely on the following preamble.

```
import AutomatePolynomial.Reflection.Polynomial.Basic
open Polynomial Rfl
```

`poly_rfl_degree_le` resolves greedy upper bounds on polynomial degree.

```
section DegreeLe
variable [Semiring R]
example : (0     : R[X]).degree ≤ ⊥ := by poly_rfl_degree_le; trivial
example : (1     : R[X]).degree ≤ 0 := by poly_rfl_degree_le; trivial
example : (X     : R[X]).degree ≤ 1 := by poly_rfl_degree_le; trivial
example : (X ^ 2 : R[X]).degree ≤ 2 := by poly_rfl_degree_le; trivial
example : (X + 1 : R[X]).degree ≤ 1 := by poly_rfl_degree_le; trivial
end DegreeLe
```

`poly_rfl_degree_eq` resolves exact degrees in some simple cases. However, when leading terms cancel, further verifiection is necessary as in the demonstrations that follow this one. `poly_rfl_leading_coeff` for leading coefficients functions similarly.

```
section DegreeEq
variable [Semiring R]
example : (0 : R[X]).degree = ⊥ := by poly_rfl_degree_eq
end DegreeEq

section DegreeEqNontrivial
variable [Semiring R] [Nontrivial R]
example : (1     : R[X]).degree = 0 := by poly_rfl_degree_eq
example : (X     : R[X]).degree = 1 := by poly_rfl_degree_eq
example : (X ^ 2 : R[X]).degree = 2 := by poly_rfl_degree_eq
end DegreeEqNontrivial
```

`poly_rfl_degree_eq_tring` resolves exact degrees by applying the additional helper tactic `poly_infer_try` at certain steps to verify that leading terms do not cancel. However, when leading terms do cancel, further verifiection is necessary as in the demonstrations that follow this one. `poly_rfl_leading_coeff_trying` for leading coefficients functions similarly.

```
section DegreeEqNontrivial
variable [Semiring R] [Nontrivial R]
example : (X + 1 : R[X]).degree = 1 := by poly_rfl_degree_eq_trying <:> poly_infer_try
end DegreeEqNontrivial
```

`poly_rfl_degree_eq_of_coeffs` resolves exact degrees by constructing a computable representation—`CoeffsList` in this case—of the entire polynomial. `poly_rfl_leading_coeff_of_coeffs` for leading coefficients, `poly_rfl_coeff` for arbitrary coefficients, and `poly_rfl_eval` for evaluations function similarly.

```
section DegreeEqOfCoeffs
example : (X + 1 : ℕ[X]).degree = 1 := by poly_rfl_degree_eq_of_coeffs VIA CoeffsList; simp; trivial
end DegreeEqOfCoeffs
```

## Ongoing Work

The listed tasks outline ongiong work and promising directions for future work, in roughly decreasing order by the scope of the task. We use tags to indicate the types of contributions entailed by each task.

### Tasks

- Multivariate system in branch [feature/mvpoly](https://github.com/LiamSchilling/AutomatePolynomial/tree/feature/mvpoly) - *feature*
    - Lemmas for `weightedTotalDegree` - *mathlib*
        - Provide closed form for cases such as `p + q`, `p * q`, and `p ^ n`
        - Show that `totalDegree` and `degreeOf` are special cases
- Reflection tactics using `Poly` and its built-in automated construction - *feature, mathlib, docs*
- Representations in univariate system - *feature, docs*
    - `CoeffList` as representation for evaluations
    - `Poly` as representation for coefficients and evaluations
- TODOs in section [Univariate System](https://liamschilling.github.io/AutomatePolynomial/blueprint/sec-univariate.html) in blueprint - *docs*
- Rendering of math symbols in [pdf blueprint](https://liamschilling.github.io/AutomatePolynomial/blueprint.pdf) - *fix*

### Tags

Some tags adapted from [Conventional Commits](https://www.conventionalcommits.org/en/v1.0.0/)

- *feature* - introduces a new feature to the codebase
- *mathlib* - entails a contribution to Mathlib
- *docs* - introduces a new unit to the documentation
- *fix* - patches a bug in the codebase
- *style* - modifies a sylistic standard of the codebase or associated documents
- *refactor* - modifies a structural standard of the codebase or associated documents

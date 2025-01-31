# Automate Polynomial
This project aims to automate proofs
about polynomial degree, coefficients, and evaluation
in Lean 4.

### Note
* `R` is some space: `R : Type*`
* `R` forms a semiring: `[Semiring R]`
* `p` and `q` are polynomials over `R`: `p : R[X]`, `q : R[X]`

## Goals
* Degree equality: `p.degree = D` where `D : WithBot Nat`
* Degree upper bounds: `p.degree <= D` where `D : WithBot Nat`
* General coefficient equality: `p.coeff = C` where `C : Nat -> R`
* Leading coefficient equality: `p.leadingCoeff = c` where `c : R`
* Evaluation equality: `p.eval = f` where `f : R -> R`

## Approach
By defining type class instances for base cases such as
the zero polynomial `0`,
constant polynomials `C c` where `c : R`,
the identity polynomial `X`, etc.,
and instances for closure over operations such as
power `p ^ n` where `n : Nat`, addition `p + q`, multiplication `p * q`, etc.,
automation is achieved by Lean's type class inference.
Type classes achieving this contain two essential components:

* a value specifying some information about the polynomial
* proof that the polynomial conforms to the specification

In order for the inferred instance's proof
to resolve a proposition,
the inference rules (type class instances) must define the specifier value
in such a way that it sufficiently reduces
to match its representation in the proposition.
For representations which lead to useful results,
this may require stronger assumptions about `R`,
which can themselves be resolved by type class instances
from the rule's arguments.

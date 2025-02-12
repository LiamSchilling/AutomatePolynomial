# Automate Polynomial
This project aims to automate proofs
about polynomial degree, coefficients, and evaluation
in Lean 4.

### Note
* `R` is some space: `R : Type*`
* `R` forms a semiring: `[Semiring R]`
* `p` and `q` are polynomials over `R`: `p : R[X]`, `q : R[X]`

## Goals
* General coefficient equality: `p.coeff n = c` where `n : Nat`, `c : R`
* Degree upper bounds: `p.degree <= D` where `D : WithBot Nat`
* Degree equality: `p.degree = D` where `D : WithBot Nat`
* Leading coefficient equality: `p.leadingCoeff = c` where `c : R`
* Evaluation equality: `p.eval x = y` where `x : R`, `y : R`
* Expansion equality: `p = c0 + c1 * X + ... cN * X ^ N` where
`N : Nat`, `c0 : R`, `c1 : R`, ... `cN : R`

## Approach
By defining type class instances for base cases such as
the zero polynomial `0`,
constant polynomials `C c` where `c : R`,
the identity polynomial `X`, etc.,
and instances for closure over operations such as
power `p ^ n` where `n : Nat`, addition `p + q`, multiplication `p * q`, etc.,
reflection proofs are constructed by Lean's type class inference
and other introduced search tactics.

Aligning with this idea,
we will use the term "inference rules" to refer to and interchangably with
definitions of type class instances in Lean.

### Type Classes
Type classes constructing an effetive reflection system
contain two essential components:

* a value specifying some information about the polynomial
* proof that the polynomial conforms to the specification

### Inference Rules
In order for the inferred instance's proof
to resolve a proposition,
the inference rules must define the specifier value
in such a way that it is definitionally equivalent
to its representation in the proposition.

### Inference System
To avoid circularity during the inference process,
which would have a major impact on performance,
the inference rules must abide by a directional constraint.
Namely, the result of an inference rule
should be stronger than its individual arguments.
For instance, suppose the weaker `a : A` and `b : B` together
result in the stronger `c : C`.
In this case,
we should only define the inference rule `instance : [a] -> [b] -> c`
and leave the converse `example : [c] -> a` and `example : [c] -> b`
inaccessible to the inference system.

### Tactics
Representations which lead to useful results may require stronger assumptions,
which can themselves be resolved by type class instances
from the rule's arguments.
For more general arguments than what can be inferred,
we introduce search tactics that allow the user to specify
combining tactics to try on those subgoals,
or indicate forms of subgoals that should be admitted
and have their proofs deferred to the user.

# Automate Polynomial

We aim to design one model
for proof-by-reflection systems in Lean 4
and follow this model to automate proof
of degrees, coefficients, evaluations, and expansions
for univariate and multivariate polynomials.

## Approach

We employ type class inference to construct representations
of properties of polynomials with witnesses of their correctness
from the bottom up.
To handle representations requiring more strict assumptions
(degree equality for example, which requires that leading terms do not cancel)
we implemented the tactic `infer_instance_trying`
which tries a helper tactic on any subgoal where Lean’s inference fails.

## Model

We specify three levels of abstraction.

* A **Signature** declares necessary *Inference Rules*,
which yield instances for a generic type class.
* The **Interface** extends multiple signatures
with a specified *Reflection Class* asserting the target property.
*Tactics* to automate proof of goals can be implemented
for generic representations.
* The **Implementation** instantiates an interface
with a specified *Representation*
and implements rules declared in the signatures.

## Reflection

We identified five properties relevant
to univariate and multivariate polynomials
(listed reflection classes are for univariate polynomials).

* `DegreeEq`: exact degree (*Sensitive*)
* `DegreeLe`: greedy upper bound on degree
* `LeadingCoeff`: exact leading coefficients (*Sensitive*)
* `Coeffs`: exact specification of all coefficients
* `Eval`: exact specification of evaluations at all points

Non-*Sensitive* inference rules do not depend on leading term cancellations.
This enables quick verification of an upper bound with `DegreeLe`, for example,
that is only imperfect when leading terms cancel.

*Sensitive* inference rules require proof that leading terms do not cancel.
`infer_instance_trying` treats these problems,
when represented as equivalent propositions on `LeadingCoeff` instances,
as typical subgoals and verifies them when they hold.

## Representations

We represented evaluations as lambda functions
and univariate coefficients as dense lists.
We implemented unboundedly-higher-dimensional dense lists
for multivariate coefficients,
in which index `[i,j,...k]` holds the `X^i*Y^j*...Z^k` coefficient.

## Future Work

Future work will improve the efficiency and strength
of the systems in this project.
Sparse and array representations of coefficients are priorities.
Search tactics beyond `infer_instance_trying` will also be explored
for more complete automation.

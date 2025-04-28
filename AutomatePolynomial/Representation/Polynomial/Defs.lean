import Mathlib.Algebra.Polynomial.Degree.Lemmas

namespace Polynomial

variable [Semiring R]

/-- Drops the constant term from a polynomial,
reducing the degree of the remaining terms to fill the space

`a + b * X + ... c * X ^ (n + 1)` becomes `b + ... c * X ^ n` -/
def tail (p : R[X]) :=
  ofFinsupp ⟨
    p.support.filterMap (
      match . with | 0 => none | i + 1 => i ) (
      by
        intro i1 i2 b
        cases i1 <;> intro h1; contradiction; cases i2 <;> intro h2; contradiction
        simp at h1 h2; rw[h1, h2] ),
    fun i => coeff p (i + 1),
    by
      intro i; constructor
      . sorry
      . sorry ⟩

end Polynomial

import Mathlib

/-!
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Matrix

namespace Brockian

/-- The cosine Gram matrix of a family of angles `x : Fin n → ℝ`:
its `(i, j)` entry is `cos (x i - x j)`. -/

noncomputable def traceNorm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) : ℝ :=
  ∑ i, |hA.eigenvalues i|

/-- **Cos Trace Norm 1597.**  For any angles `x : Fin n → ℝ`, the cosine Gram matrix
`C i j = cos (x i - x j)` is positive semidefinite, and hence its trace norm (the sum of the
absolute values of its eigenvalues) equals its trace, namely `n`. -/

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

lemma cosMatrix_trace {n : ℕ} (x : Fin n → ℝ) : (cosMatrix x).trace = n := by
  simp [Matrix.trace, Matrix.diag, cosMatrix]

/-- The trace norm (Schatten 1-norm) of a Hermitian real matrix: the sum of the absolute
values of its eigenvalues. -/

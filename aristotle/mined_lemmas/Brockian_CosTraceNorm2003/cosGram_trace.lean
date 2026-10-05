import Mathlib

/-!
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped MatrixOrder

namespace Brockian

open Matrix

/-- The *cosine Gram matrix* of a family of phases `θ : Fin n → ℝ`:
its `(i, j)` entry is `cos (θ i - θ j)`. -/

theorem cosGram_trace {n : ℕ} (θ : Fin n → ℝ) : (cosGram θ).trace = n := by
  simp [Matrix.trace, Matrix.diag, cosGram]

/-- **Cos Trace Norm 2003.**  For any phases `θ : Fin n → ℝ`, the cosine Gram matrix
`C i j = cos (θ i - θ j)` is positive semidefinite, has trace `n`, and its trace norm
(the sum of its singular values) is exactly `n`. -/

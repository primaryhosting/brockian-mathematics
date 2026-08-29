/-
# Cos Trace Norm 4001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm4001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cos Trace Norm 4001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm4001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Matrix
open scoped MatrixOrder

/-- The `4001 × 4001` real "cosine Gram matrix" attached to a family of angles
`θ : Fin 4001 → ℝ`, with entries `cos (θ i - θ j)`. -/

theorem trace_cosGram (θ : Fin 4001 → ℝ) : (cosGram θ).trace = 4001 := by
  simp [Matrix.trace, Matrix.diag, cosGram]

/-- **Cos Trace Norm 4001.**  For every family of angles `θ : Fin 4001 → ℝ`, the
`4001 × 4001` cosine Gram matrix `(cos (θ i - θ j))` has trace norm exactly `4001`. -/

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


open scoped BigOperators
open scoped Matrix

set_option maxRecDepth 10000

namespace Brockian

/-- The `n × n` real "cosine Gram matrix" with entries `cos (i θ - j θ)`. -/

theorem cosGram_trace (n : ℕ) (theta : ℝ) : (cosGram n theta).trace = n := by
  simp [Matrix.trace, Matrix.diag, cosGram]

/-- **General form.** For every `n` and every angle `θ`, the trace norm (sum of the absolute
values of the eigenvalues) of the `n × n` matrix `cos (i θ - j θ)` equals `n`. -/

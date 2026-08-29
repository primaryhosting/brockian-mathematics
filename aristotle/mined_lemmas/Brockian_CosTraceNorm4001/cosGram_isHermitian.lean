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

theorem cosGram_isHermitian (n : ℕ) (theta : ℝ) : (cosGram n theta).IsHermitian :=
  (cosGram_posSemidef n theta).1

/-- The trace of the `n × n` cosine Gram matrix is `n`. -/

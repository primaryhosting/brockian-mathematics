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

noncomputable def cosSinRows (n : ℕ) (theta : ℝ) : Matrix (Fin 2) (Fin n) ℝ :=
  Matrix.of fun i j => if i = 0 then Real.cos ((j : ℝ) * theta) else Real.sin ((j : ℝ) * theta)

/-- The cosine Gram matrix is the Gram matrix of the columns of `cosSinRows`. -/

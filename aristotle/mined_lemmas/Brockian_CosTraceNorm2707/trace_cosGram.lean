/- (module docstrings may not precede `import`, so the required header is kept
   verbatim inside this comment block)
/-!
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- The cosine Gram matrix of a family of angles: `C i j = cos (x i - x j)`.
It is the Gram matrix of the unit vectors `(cos (x i), sin (x i))`, hence positive
semidefinite of rank at most `2`. -/

lemma trace_cosGram {n : ℕ} (x : Fin n → ℝ) : Matrix.trace (cosGram x) = n := by
  simp [cosGram, Matrix.trace, Matrix.diag]

/-- Expansion of `tr (C U)` for the cosine Gram matrix into its two rank-one pieces. -/

/-!
# Cos Trace Norm 1279
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1279
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real

namespace Brockian

/-- The planar rotation matrix by angle `θ`. -/

theorem trace_rot (θ : ℝ) : Matrix.trace (rot θ) = 2 * Real.cos θ := by
  simp [rot, Matrix.trace_fin_two_of]
  ring

/-- The trace of a power of a rotation matrix. -/

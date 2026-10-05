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

theorem trace_rot_pow (θ : ℝ) (n : ℕ) :
    Matrix.trace ((rot θ) ^ n) = 2 * Real.cos (n * θ) := by
  rw [rot_pow, trace_rot]

/-- `|cos x| = 1` exactly when `sin x = 0`. -/

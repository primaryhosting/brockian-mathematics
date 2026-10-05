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

theorem rot_pow (θ : ℝ) : ∀ n : ℕ, (rot θ) ^ n = rot (n * θ)
  | 0 => by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [rot, Matrix.one_apply]
  | (n + 1) => by
      rw [pow_succ, rot_pow θ n, rot_mul]
      push_cast
      ring_nf

/-- The trace of a rotation matrix. -/

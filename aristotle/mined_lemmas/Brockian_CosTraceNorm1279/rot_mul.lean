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

theorem rot_mul (θ φ : ℝ) : rot θ * rot φ = rot (θ + φ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_succ, Real.cos_add, Real.sin_add] <;> ring

/-- Powers of a rotation are rotations. -/

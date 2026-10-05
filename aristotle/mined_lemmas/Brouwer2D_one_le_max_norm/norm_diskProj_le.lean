/-
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Complex Metric Set

namespace Brouwer2D

/-! ### The radial retraction of the plane onto the closed unit disk -/

/-- The radial retraction of `ℂ` onto the closed unit disk. -/

lemma norm_diskProj_le (z : ℂ) : ‖diskProj z‖ ≤ 1 := by
  have h1 : (0 : ℝ) < max 1 ‖z‖ := lt_of_lt_of_le one_pos (one_le_max_norm z)
  have : ‖diskProj z‖ = ‖z‖ / max 1 ‖z‖ := by
    rw [diskProj, norm_smul]
    simp [abs_of_pos h1, div_eq_inv_mul]
  rw [this, div_le_one h1]
  exact le_max_right _ _


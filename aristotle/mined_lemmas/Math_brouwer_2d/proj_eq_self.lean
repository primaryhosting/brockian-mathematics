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

open Metric Set Complex

namespace Math

noncomputable section

/-! ## Step 1: the radial projection onto the closed unit disk of `ℂ`. -/

/-- Radial projection of `ℂ` onto the closed unit disk. -/

lemma proj_eq_self {z : ℂ} (hz : ‖z‖ ≤ 1) : proj z = z := by
  rw [proj, max_eq_left hz]
  simp

/-! ## Step 2: no continuous retraction of `ℂ` onto the unit circle. -/

/-- There is no continuous map `ℂ → ℂ` with values in the unit circle which is the
identity on the unit circle. -/

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

lemma norm_proj_le (z : ℂ) : ‖proj z‖ ≤ 1 := by
  have h1 : (1:ℝ) ≤ max 1 ‖z‖ := le_max_left _ _
  have h2 : ‖z‖ ≤ max 1 ‖z‖ := le_max_right _ _
  rw [proj, norm_smul]
  simp only [norm_inv, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ max 1 ‖z‖)]
  rw [inv_mul_le_iff₀ (by linarith)]
  linarith


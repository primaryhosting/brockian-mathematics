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

lemma continuous_proj : Continuous proj := by
  apply Continuous.smul _ continuous_id
  exact (continuous_const.max continuous_norm).inv₀ (fun z => by positivity)


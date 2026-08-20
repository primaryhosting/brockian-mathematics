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

theorem brouwer_disk_complex (f : ℂ → ℂ) (hf : ContinuousOn f (closedBall 0 1))
    (hmaps : MapsTo f (closedBall 0 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : ℂ) 1, f x = x := by
  by_contra h
  push_neg at h
  obtain ⟨g, hg, hnorm, hbdry⟩ := exists_retraction_of_no_fixed_point f hf hmaps h
  exact no_retraction g hg hnorm hbdry

/-- **Brouwer's fixed point theorem in dimension 2**: every continuous self-map of the
closed 2-dimensional disk has a fixed point. -/

import Mathlib

/-!
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Complex

namespace Math

/-- One primitive 6-th root of unity: `1/2 + (√3/2) i`. -/

lemma zeta6'_ne_real (r : ℝ) : zeta6' ≠ (r : ℂ) := by
  intro h
  have := congrArg Complex.im h
  rw [zeta6'_im] at this
  simp at this


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

lemma zeta6_add_zeta6' : zeta6 + zeta6' = 1 := by
  simp only [zeta6, zeta6']
  ring


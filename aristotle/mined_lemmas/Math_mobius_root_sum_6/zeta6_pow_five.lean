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

lemma zeta6_pow_five : zeta6 ^ 5 = 1 - zeta6 := by
  linear_combination zeta6 ^ 2 * zeta6_cube - zeta6_sq


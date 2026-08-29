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

lemma zeta6_mul_zeta6' : zeta6 * zeta6' = 1 := by
  simp only [zeta6, zeta6']
  linear_combination (-(Complex.I ^ 2) / 4) * sqrt3_sq - (3 / 4 : ℂ) * Complex.I_sq

/-- A complex number is a primitive 6-th root of unity iff it is `zeta6` or `zeta6'`. -/

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

/-- A fixed primitive 6-th root of unity in `ℂ`. -/

lemma zeta6_ne_pow_five : zeta6 ≠ zeta6 ^ 5 := by
  intro h
  have := isPrimitiveRoot_zeta6.pow_inj (i := 1) (j := 5) (by norm_num) (by norm_num)
    (by simpa using h)
  omega


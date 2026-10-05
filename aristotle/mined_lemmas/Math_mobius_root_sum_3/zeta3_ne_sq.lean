/-
# Mobius Root Sum 3
Category: Pure Mathematics
Target: Math.mobius_root_sum_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 3
Category: Pure Mathematics
Target: Math.mobius_root_sum_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- A fixed primitive cube root of unity in `ℂ`. -/

lemma zeta3_ne_sq : zeta3 ≠ zeta3 ^ 2 := by
  intro h
  have hz := isPrimitiveRoot_zeta3
  have hz0 : zeta3 ≠ 0 := by
    intro h0
    have := hz.pow_eq_one
    rw [h0] at this
    norm_num at this
  have hmul : zeta3 * (zeta3 - 1) = 0 := by linear_combination -h
  rcases mul_eq_zero.1 hmul with h' | h'
  · exact hz0 h'
  · rw [sub_eq_zero.1 h'] at hz
    have := hz.unique (IsPrimitiveRoot.one)
    omega


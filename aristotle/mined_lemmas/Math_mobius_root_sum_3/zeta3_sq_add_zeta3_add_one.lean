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

lemma zeta3_sq_add_zeta3_add_one : zeta3 ^ 2 + zeta3 + 1 = 0 := by
  have h1 : zeta3 ^ 3 = 1 := isPrimitiveRoot_zeta3.pow_eq_one
  have h2 : zeta3 ≠ 1 := by
    intro h
    have := isPrimitiveRoot_zeta3
    rw [h] at this
    have := this.unique (IsPrimitiveRoot.one)
    omega
  have h3 : (zeta3 - 1) * (zeta3 ^ 2 + zeta3 + 1) = 0 := by ring_nf; linear_combination h1
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd (sub_eq_zero.1 h) h2
  · exact h


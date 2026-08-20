/-
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open ArithmeticFunction Finset

/-- The Möbius function at `10` equals `1`. -/

lemma pow_ne_pow {ζ : ℂ} (h : IsPrimitiveRoot ζ 10) {i j : ℕ} (hi : i < 10) (hj : j < 10)
    (hij : i ≠ j) : ζ ^ i ≠ ζ ^ j := fun hc => hij (h.pow_inj hi hj hc)


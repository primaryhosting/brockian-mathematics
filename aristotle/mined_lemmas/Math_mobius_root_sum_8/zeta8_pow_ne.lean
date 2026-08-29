/-
# Mobius Root Sum 8
Category: Pure Mathematics
Target: Math.mobius_root_sum_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

/-- A fixed primitive `8`-th root of unity in `ℂ`. -/

theorem zeta8_pow_ne (i j : ℕ) (hi : i < 8) (hj : j < 8) (hij : i ≠ j) :
    zeta8 ^ i ≠ zeta8 ^ j :=
  fun h => hij (isPrimitiveRoot_zeta8.pow_inj hi hj h)

/-- The primitive `8`-th roots of unity are exactly `ζ, ζ³, ζ⁵, ζ⁷`. -/

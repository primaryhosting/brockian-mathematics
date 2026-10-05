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

theorem isPrimitiveRoot_zeta8 : IsPrimitiveRoot zeta8 8 := by
  simpa [zeta8] using Complex.isPrimitiveRoot_exp 8 (by norm_num)


/-
# Mobius Root Sum 3
Category: Pure Mathematics
Target: Math.mobius_root_sum_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

open Finset ArithmeticFunction ArithmeticFunction.Moebius

/-- `ζ = exp (2 π i / 3)` is a primitive cube root of unity. -/

theorem isPrimitiveRoot_exp_three :
    IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 3)) 3 :=
  Complex.isPrimitiveRoot_exp 3 (by norm_num)

/-- `ζ ≠ ζ²` for `ζ = exp (2 π i / 3)`. -/

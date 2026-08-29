import Mathlib

/-!
# Mobius Root Sum 7
Category: Pure Mathematics
Target: Math.mobius_root_sum_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- A fixed primitive 7-th root of unity in `ℂ`. -/
private noncomputable def zeta7 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 7)


private theorem isPrimitiveRoot_zeta7 : IsPrimitiveRoot zeta7 7 :=
  Complex.isPrimitiveRoot_exp 7 (by norm_num)

/-- The primitive 7-th roots of unity are exactly `ζ^k` for `1 ≤ k < 7`. -/

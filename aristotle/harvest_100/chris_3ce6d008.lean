import Mathlib

/-!
# Mobius Root Sum 1
Category: Pure Mathematics
Target: Math.mobius_root_sum_1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open Finset

/-- The set of primitive `1`-th roots of unity in `ℂ` is `{1}`. -/
theorem primitiveRoots_one_complex : primitiveRoots 1 ℂ = {1} := by
  ext x
  rw [mem_primitiveRoots one_pos]
  simp [IsPrimitiveRoot.one_right_iff]

/-- The sum of the primitive `1`-th roots of unity equals `μ 1`. -/
theorem mobius_root_sum_1 :
    ∑ z ∈ primitiveRoots 1 ℂ, z = (ArithmeticFunction.moebius 1 : ℂ) := by
  rw [primitiveRoots_one_complex]
  simp

end Math


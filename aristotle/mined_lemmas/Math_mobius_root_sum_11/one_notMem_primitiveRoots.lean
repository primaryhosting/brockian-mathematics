/-
# Mobius Root Sum 11
Category: Pure Mathematics
Target: Math.mobius_root_sum_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 11

The sum of the primitive 11-th roots of unity in `ℂ` equals `μ(11)`.
-/

open Finset Polynomial

namespace Math

/-- The 11-th roots of unity in `ℂ` are exactly the powers `ζ ^ i`, `i < 11`, of a primitive
11-th root of unity `ζ`. -/

lemma one_notMem_primitiveRoots : (1 : ℂ) ∉ primitiveRoots 11 ℂ := by
  intro hmem
  have := isPrimitiveRoot_of_mem_primitiveRoots hmem
  have := this.unique (IsPrimitiveRoot.one_right_iff.2 rfl)
  omega

/-- **Mobius root sum 11**: the sum of the primitive 11-th roots of unity in `ℂ` equals
`μ(11) = -1`. -/

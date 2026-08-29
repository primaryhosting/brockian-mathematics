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

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

/-- Every primitive cube root of unity satisfies `x ^ 2 + x + 1 = 0`. -/

lemma sq_add_self_add_one_eq_zero_of_mem_primitiveRoots_three
    {x : ℂ} (hx : x ∈ primitiveRoots 3 ℂ) : x ^ 2 + x + 1 = 0 := by
  rw [mem_primitiveRoots (by norm_num)] at hx
  have h1 : x ^ 3 = 1 := hx.pow_eq_one
  have h2 : x ≠ 1 := hx.ne_one (by norm_num)
  have hfac : (x - 1) * (x ^ 2 + x + 1) = 0 := by ring_nf; linear_combination h1
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (sub_eq_zero.mp h) h2
  · exact h

/-- The sum of the primitive `3`-rd roots of unity equals `μ 3`. -/

import Mathlib

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

import Mathlib
/-!
# Mobius Root Sum 5
Category: Pure Mathematics
Target: Math.mobius_root_sum_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- The primitive 5-th roots of unity in `ℂ` are exactly `ζ, ζ², ζ³, ζ⁴`
for any fixed primitive 5-th root `ζ`. -/

theorem sum_pow_primitive_five {ζ : ℂ} (h : IsPrimitiveRoot ζ 5) :
    ∑ i ∈ Finset.Icc 1 4, ζ ^ i = -1 := by
  have h5 : ζ ^ 5 = 1 := h.pow_eq_one
  have hne : ζ - 1 ≠ 0 := sub_ne_zero.mpr (fun hc => by
    rw [hc] at h; exact absurd (IsPrimitiveRoot.unique h IsPrimitiveRoot.one) (by norm_num))
  have hexp : ∑ i ∈ Finset.Icc 1 4, ζ ^ i = ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 := by
    simp [Finset.sum_Icc_succ_top]
  have key : (ζ - 1) * (∑ i ∈ Finset.Icc 1 4, ζ ^ i - -1) = 0 := by
    rw [hexp]; linear_combination h5
  have := (mul_eq_zero.mp key).resolve_left hne
  linear_combination this

/-- The sum of the primitive 5-th roots of unity equals `μ(5) = -1`. -/

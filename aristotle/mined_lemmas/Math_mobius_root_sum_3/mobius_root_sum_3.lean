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

theorem mobius_root_sum_3 :
    ∑ z ∈ primitiveRoots 3 ℂ, z = (μ 3 : ℤ) := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3) with hζdef
  have hζ : IsPrimitiveRoot ζ 3 := isPrimitiveRoot_exp_three
  have hne : ζ ≠ ζ ^ 2 := exp_three_ne_sq
  have hgeom : ∑ i ∈ Finset.range 3, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero] at hgeom
  rw [primitiveRoots_three_eq, Finset.sum_insert (by simpa using hne), Finset.sum_singleton,
    moebius_apply_prime (by norm_num)]
  push_cast
  linear_combination hgeom

end Math

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


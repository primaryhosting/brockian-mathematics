/-
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- The Möbius function at `6` equals `1` (since `6 = 2 * 3` is squarefree with two prime
factors). -/

theorem mobius_root_sum_6 :
    ∑ z ∈ primitiveRoots 6 ℂ, z = (ArithmeticFunction.moebius 6 : ℂ) := by
  have h : IsPrimitiveRoot (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 6)) 6 :=
    Complex.isPrimitiveRoot_exp 6 (by norm_num)
  set z := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 6)
  have hz2 : z ^ 2 - z + 1 = 0 := cyclotomic_six_eq_zero_of_isPrimitiveRoot h
  have hne : z ≠ z ^ 5 := by
    intro he
    have h1 : 2 * z - 1 = 0 := by linear_combination he + (z ^ 3 + z ^ 2 - 1) * hz2
    have h3 : (3 : ℂ) = 0 := by linear_combination 4 * hz2 - (2 * z - 1) * h1
    norm_num at h3
  rw [primitiveRoots_six_eq h, Finset.sum_insert (by simpa using hne), Finset.sum_singleton,
    moebius_six]
  push_cast
  linear_combination (z ^ 3 + z ^ 2 - 1) * hz2

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


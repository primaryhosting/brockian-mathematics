/-
# Mobius Root Sum 3
Category: Pure Mathematics
Target: Math.mobius_root_sum_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring, so the header above is
-- repeated as the module docstring immediately after the import.)

import Mathlib

/-!
# Mobius Root Sum 3
Category: Pure Mathematics
Target: Math.mobius_root_sum_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Complex

namespace Math

open scoped ArithmeticFunction.Moebius

/-- `ω = exp(2πi/3)` is a primitive cube root of unity. -/
theorem isPrimitiveRoot_exp_three :
    IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 3)) 3 :=
  Complex.isPrimitiveRoot_exp 3 (by norm_num)

/-- The finset of primitive cube roots of unity in `ℂ` is `{ω, ω²}`. -/
theorem primitiveRoots_three_eq :
    primitiveRoots 3 ℂ =
      ({Complex.exp (2 * Real.pi * Complex.I / 3),
        Complex.exp (2 * Real.pi * Complex.I / 3) ^ 2} : Finset ℂ) := by
  set ω := Complex.exp (2 * Real.pi * Complex.I / 3) with hωdef
  have hω : IsPrimitiveRoot ω 3 := isPrimitiveRoot_exp_three
  have hne : ω ≠ ω ^ 2 := by
    intro h
    have : ω ^ 1 = ω ^ 2 := by simpa using h
    have := hω.pow_inj (by norm_num) (by norm_num) this
    omega
  have hsub : ({ω, ω ^ 2} : Finset ℂ) ⊆ primitiveRoots 3 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [mem_primitiveRoots (by norm_num)]
    rcases hx with rfl | rfl
    · exact hω
    · exact hω.pow_of_coprime 2 (by decide)
  have hcard : #(primitiveRoots 3 ℂ) = 2 := by
    rw [hω.card_primitiveRoots]
    decide
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [hcard, Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]

/-- The sum of the primitive cube roots of unity equals `μ 3`. -/
theorem mobius_root_sum_3 :
    ∑ z ∈ primitiveRoots 3 ℂ, z = (μ 3 : ℂ) := by
  set ω := Complex.exp (2 * Real.pi * Complex.I / 3) with hωdef
  have hω : IsPrimitiveRoot ω 3 := isPrimitiveRoot_exp_three
  have hgeom : ∑ i ∈ Finset.range 3, ω ^ i = 0 := hω.geom_sum_eq_zero (by norm_num)
  have hsum : 1 + ω + ω ^ 2 = 0 := by
    simpa [Finset.sum_range_succ, add_comm, add_assoc, add_left_comm] using hgeom
  have hne : ω ≠ ω ^ 2 := by
    intro h
    have : ω ^ 1 = ω ^ 2 := by simpa using h
    have := hω.pow_inj (by norm_num) (by norm_num) this
    omega
  have hmu : (μ 3 : ℤ) = -1 := by
    rw [ArithmeticFunction.moebius_apply_prime (by norm_num)]
  rw [primitiveRoots_three_eq, Finset.sum_insert (by simpa using hne), Finset.sum_singleton,
    hmu]
  push_cast
  linear_combination hsum

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


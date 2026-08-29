import Mathlib

/-!
# Mobius Root Sum 3
Category: Pure Mathematics
Target: Math.mobius_root_sum_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Math

/-- The set of primitive cube roots of unity in `ℂ` is `{ζ, ζ ^ 2}` for
`ζ = exp (2 π i / 3)`. -/
theorem primitiveRoots_three_eq (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 3) :
    primitiveRoots 3 ℂ = {ζ, ζ ^ 2} := by
  have hne : ζ ≠ ζ ^ 2 := by
    intro h
    have := hζ.pow_inj (i := 1) (j := 2) (by norm_num) (by norm_num) (by simpa using h)
    omega
  have hsub : ({ζ, ζ ^ 2} : Finset ℂ) ⊆ primitiveRoots 3 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (mem_primitiveRoots (by norm_num)).2 hζ
    · exact (mem_primitiveRoots (by norm_num)).2
        (hζ.pow_of_coprime 2 (by decide))
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [hζ.card_primitiveRoots, Finset.card_insert_of_notMem (by simpa using hne),
    Finset.card_singleton]
  decide

/-- The sum of the primitive cube roots of unity in `ℂ` equals `μ 3 = -1`. -/
theorem mobius_root_sum_3 :
    ∑ z ∈ primitiveRoots 3 ℂ, z = (ArithmeticFunction.moebius 3 : ℂ) := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3) with hζdef
  have hζ : IsPrimitiveRoot ζ 3 := by
    simpa [hζdef, mul_comm, mul_assoc, mul_left_comm] using
      Complex.isPrimitiveRoot_exp 3 (by norm_num)
  have hgeom : ∑ i ∈ Finset.range 3, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  have hsum : ζ + ζ ^ 2 = -1 := by
    simp [Finset.sum_range_succ] at hgeom
    linear_combination hgeom
  have hne : ζ ≠ ζ ^ 2 := by
    intro h
    have := hζ.pow_inj (i := 1) (j := 2) (by norm_num) (by norm_num) (by simpa using h)
    omega
  rw [primitiveRoots_three_eq ζ hζ, Finset.sum_insert (by simpa using hne),
    Finset.sum_singleton, hsum]
  have : ArithmeticFunction.moebius 3 = -1 := by
    have h3 : Nat.Prime 3 := by norm_num
    simpa using ArithmeticFunction.moebius_apply_prime h3
  rw [this]
  norm_num

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


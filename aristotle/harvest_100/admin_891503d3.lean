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
theorem exp_three_ne_sq :
    Complex.exp (2 * Real.pi * Complex.I / 3) ≠
      Complex.exp (2 * Real.pi * Complex.I / 3) ^ 2 := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3) with hζdef
  have hζ : IsPrimitiveRoot ζ 3 := isPrimitiveRoot_exp_three
  intro h
  have hz : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have h1 : ζ = 1 := by
    have hmul : ζ * 1 = ζ * ζ := by rw [mul_one, ← pow_two, ← h]
    exact (mul_left_cancel₀ hz hmul).symm
  rw [h1] at hζ
  have h31 : (3 : ℕ) = 1 := hζ.unique IsPrimitiveRoot.one
  omega

/-- The set of primitive cube roots of unity in `ℂ` is `{ζ, ζ²}` for
`ζ = exp (2 π i / 3)`. -/
theorem primitiveRoots_three_eq :
    primitiveRoots 3 ℂ = {Complex.exp (2 * Real.pi * Complex.I / 3),
      Complex.exp (2 * Real.pi * Complex.I / 3) ^ 2} := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3) with hζdef
  have hζ : IsPrimitiveRoot ζ 3 := isPrimitiveRoot_exp_three
  have hne : ζ ≠ ζ ^ 2 := exp_three_ne_sq
  have hsub : ({ζ, ζ ^ 2} : Finset ℂ) ⊆ primitiveRoots 3 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (mem_primitiveRoots (by norm_num)).2 hζ
    · exact (mem_primitiveRoots (by norm_num)).2 (hζ.pow_of_coprime 2 (by decide))
  have hcard : (primitiveRoots 3 ℂ).card = 2 := by
    rw [hζ.card_primitiveRoots]; decide
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [hcard, Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]

/-- The sum of the primitive `3`-rd roots of unity in `ℂ` equals `μ 3`. -/
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


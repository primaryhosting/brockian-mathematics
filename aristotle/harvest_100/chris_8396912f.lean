/-
# Mobius Root Sum 3
Category: Pure Mathematics
Target: Math.mobius_root_sum_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

open Finset Complex

/-- The primitive cube roots of unity in `ℂ` are exactly `ζ` and `ζ ^ 2`,
where `ζ = exp (2 * π * I / 3)`. -/
lemma primitiveRoots_three_eq :
    primitiveRoots 3 ℂ = {Complex.exp (2 * Real.pi * Complex.I / 3),
      Complex.exp (2 * Real.pi * Complex.I / 3) ^ 2} := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3) with hζdef
  have hζ : IsPrimitiveRoot ζ 3 := by
    have := Complex.isPrimitiveRoot_exp 3 (by norm_num)
    simpa [hζdef] using this
  have hne : ζ ≠ ζ ^ 2 := by
    intro h
    have : (1 : ℕ) = 2 := hζ.pow_inj (by norm_num) (by norm_num) (by simpa using h)
    omega
  have hsub : ({ζ, ζ ^ 2} : Finset ℂ) ⊆ primitiveRoots 3 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (mem_primitiveRoots (by norm_num)).2 hζ
    · exact (mem_primitiveRoots (by norm_num)).2 (hζ.pow_of_coprime 2 (by norm_num))
  have hcard : (primitiveRoots 3 ℂ).card ≤ ({ζ, ζ ^ 2} : Finset ℂ).card := by
    rw [Complex.card_primitiveRoots, Finset.card_insert_of_notMem (by simpa using hne),
      Finset.card_singleton]
    decide
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

/-- The sum of the primitive `3`-rd roots of unity equals `μ 3 = -1`. -/
theorem mobius_root_sum_3 :
    ∑ ζ ∈ primitiveRoots 3 ℂ, ζ = (ArithmeticFunction.moebius 3 : ℂ) := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3) with hζdef
  have hζ : IsPrimitiveRoot ζ 3 := by
    have := Complex.isPrimitiveRoot_exp 3 (by norm_num)
    simpa [hζdef] using this
  have hne : ζ ≠ ζ ^ 2 := by
    intro h
    have : (1 : ℕ) = 2 := hζ.pow_inj (by norm_num) (by norm_num) (by simpa using h)
    omega
  have hgeom : ∑ i ∈ Finset.range 3, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  have hsum : 1 + ζ + ζ ^ 2 = 0 := by
    simpa [Finset.sum_range_succ, add_comm, add_assoc, add_left_comm] using hgeom
  have hmu : (ArithmeticFunction.moebius 3 : ℂ) = -1 := by
    rw [ArithmeticFunction.moebius_apply_prime (by norm_num)]
    norm_num
  rw [primitiveRoots_three_eq, hmu, ← hζdef, Finset.sum_insert (by simpa using hne),
    Finset.sum_singleton]
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


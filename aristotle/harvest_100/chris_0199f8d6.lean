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

theorem mobius_root_sum_3 :
    ∑ z ∈ primitiveRoots 3 ℂ, z = (ArithmeticFunction.moebius 3 : ℂ) := by
  have hz : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 3)) 3 :=
    Complex.isPrimitiveRoot_exp 3 (by norm_num)
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3) with hζdef
  have hne : ζ ≠ ζ ^ 2 := by
    intro h
    have := (hz.pow_inj (i := 1) (j := 2) (by norm_num) (by norm_num))
    simp only [pow_one] at this
    exact absurd (this h) (by norm_num)
  have hsub : ({ζ, ζ ^ 2} : Finset ℂ) ⊆ primitiveRoots 3 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (mem_primitiveRoots (by norm_num)).mpr hz
    · exact (mem_primitiveRoots (by norm_num)).mpr
        (hz.pow_of_coprime 2 (by norm_num))
  have hcard : (primitiveRoots 3 ℂ).card ≤ ({ζ, ζ ^ 2} : Finset ℂ).card := by
    rw [hz.card_primitiveRoots, Finset.card_insert_of_notMem (by simpa using hne),
      Finset.card_singleton]
    decide
  have heq : ({ζ, ζ ^ 2} : Finset ℂ) = primitiveRoots 3 ℂ :=
    Finset.eq_of_subset_of_card_le hsub hcard
  have hgeom : ∑ i ∈ Finset.range 3, ζ ^ i = 0 := hz.geom_sum_eq_zero (by norm_num)
  rw [← heq, Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at hgeom
  have : ArithmeticFunction.moebius 3 = -1 := by
    simp [ArithmeticFunction.moebius_apply_prime Nat.prime_three]
  rw [this]
  push_cast
  linear_combination hgeom

end Math


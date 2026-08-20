import Mathlib

/-!
# Mobius Root Sum 7
Category: Pure Mathematics
Target: Math.mobius_root_sum_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- With `ζ = exp(2πi/7)`, the primitive 7-th roots of unity are exactly the
powers `ζ^i` for `1 ≤ i < 7`. -/
lemma primitiveRoots_seven_eq_image :
    primitiveRoots 7 ℂ =
      (Finset.Ico 1 7).image fun i : ℕ => Complex.exp (2 * Real.pi * Complex.I / 7) ^ i := by
  classical
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 7) with hζdef
  have hζ : IsPrimitiveRoot ζ 7 := by
    have := Complex.isPrimitiveRoot_exp 7 (by norm_num)
    simpa [hζdef, mul_comm, mul_assoc, mul_left_comm] using this
  have hsub : (Finset.Ico 1 7).image (fun i : ℕ => ζ ^ i) ⊆ primitiveRoots 7 ℂ := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_Ico] at hx
    obtain ⟨i, ⟨hi1, hi7⟩, rfl⟩ := hx
    rw [mem_primitiveRoots (by norm_num)]
    refine hζ.pow_of_coprime i ?_
    interval_cases i <;> decide
  have hcard : (primitiveRoots 7 ℂ).card ≤ ((Finset.Ico 1 7).image fun i : ℕ => ζ ^ i).card := by
    rw [Finset.card_image_of_injOn, Nat.card_Ico, Complex.card_primitiveRoots]
    · decide
    · intro i hi j hj e
      simp only [Finset.coe_Ico, Set.mem_Ico] at hi hj
      exact hζ.pow_inj (by omega) (by omega) e
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

/-- The sum of the primitive 7-th roots of unity equals `μ(7) = -1`. -/
theorem mobius_root_sum_7 :
    ∑ z ∈ primitiveRoots 7 ℂ, z = (ArithmeticFunction.moebius 7 : ℂ) := by
  classical
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 7) with hζdef
  have hζ : IsPrimitiveRoot ζ 7 := by
    have := Complex.isPrimitiveRoot_exp 7 (by norm_num)
    simpa [hζdef, mul_comm, mul_assoc, mul_left_comm] using this
  have hgeom : ∑ i ∈ Finset.range 7, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  have hsum : ∑ z ∈ primitiveRoots 7 ℂ, z = ∑ i ∈ Finset.Ico 1 7, ζ ^ i := by
    rw [primitiveRoots_seven_eq_image]
    refine Finset.sum_image ?_
    intro i hi j hj e
    simp only [Finset.coe_Ico, Set.mem_Ico] at hi hj
    exact hζ.pow_inj (by omega) (by omega) e
  have hsplit : ∑ i ∈ Finset.range 7, ζ ^ i = 1 + ∑ i ∈ Finset.Ico 1 7, ζ ^ i := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by norm_num : (0:ℕ) < 7)]
    simp
  have hmu : (ArithmeticFunction.moebius 7 : ℂ) = -1 := by
    rw [ArithmeticFunction.moebius_apply_prime (by norm_num)]
    norm_num
  rw [hsum, hmu]
  have : (1 : ℂ) + ∑ i ∈ Finset.Ico 1 7, ζ ^ i = 0 := by rw [← hsplit, hgeom]
  linear_combination this

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


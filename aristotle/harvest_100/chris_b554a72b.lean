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

/-
# Mobius Root Sum 5
Category: Pure Mathematics
Target: Math.mobius_root_sum_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 5
Category: Pure Mathematics
Target: Math.mobius_root_sum_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open Finset Polynomial

namespace Math

/-- A fixed primitive 5-th root of unity in `ℂ`. -/
noncomputable def zeta5 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

lemma isPrimitiveRoot_zeta5 : IsPrimitiveRoot zeta5 5 :=
  Complex.isPrimitiveRoot_exp 5 (by norm_num)

/-- The primitive 5-th roots of unity are exactly `ζ, ζ², ζ³, ζ⁴`. -/
lemma primitiveRoots_five_eq :
    primitiveRoots 5 ℂ = (Finset.Ico 1 5).image (fun k => zeta5 ^ k) := by
  have hζ := isPrimitiveRoot_zeta5
  ext x
  simp only [mem_primitiveRoots (by norm_num : 0 < 5), Finset.mem_image, Finset.mem_Ico]
  constructor
  · intro hx
    obtain ⟨k, hk, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx.pow_eq_one
    refine ⟨k, ⟨?_, hk⟩, rfl⟩
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp only [pow_zero] at hx
      simpa using hx.unique IsPrimitiveRoot.one
    · exact h
  · rintro ⟨k, ⟨hk1, hk5⟩, rfl⟩
    refine hζ.pow_of_coprime k ?_
    interval_cases k <;> decide

/-- The sum of the primitive 5-th roots of unity equals `μ(5)`. -/
theorem mobius_root_sum_5 :
    ∑ z ∈ primitiveRoots 5 ℂ, z = (ArithmeticFunction.moebius 5 : ℂ) := by
  have hζ := isPrimitiveRoot_zeta5
  have hgeom : ∑ k ∈ Finset.range 5, zeta5 ^ k = 0 := hζ.geom_sum_eq_zero (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, zero_add] at hgeom
  have hmu : (ArithmeticFunction.moebius 5 : ℂ) = -1 := by
    rw [ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5)]
    norm_num
  rw [primitiveRoots_five_eq, Finset.sum_image, hmu]
  · rw [show Finset.Ico 1 5 = ({1, 2, 3, 4} : Finset ℕ) by decide]
    norm_num [Finset.sum_insert, Finset.sum_singleton]
    linear_combination hgeom
  · intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    exact hζ.pow_inj (by omega) (by omega) hab

end Math


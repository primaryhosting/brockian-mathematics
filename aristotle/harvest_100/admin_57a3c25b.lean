import Mathlib

/-!
# Mobius Root Sum 7
Category: Pure Mathematics
Target: Math.mobius_root_sum_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset ArithmeticFunction

namespace Math

/-- For a primitive `7`-th root of unity `ζ`, the primitive `7`-th roots of unity are
exactly `ζ ^ i` for `1 ≤ i < 7`. -/
lemma primitiveRoots_seven_eq_image {ζ : ℂ} (h : IsPrimitiveRoot ζ 7) :
    primitiveRoots 7 ℂ = (Finset.Ico 1 7).image (fun i => ζ ^ i) := by
  ext x
  simp only [mem_primitiveRoots (by norm_num : (0:ℕ) < 7), Finset.mem_image, Finset.mem_Ico]
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := h.eq_pow_of_pow_eq_one hx.pow_eq_one
    refine ⟨i, ⟨?_, hi⟩, rfl⟩
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp only [pow_zero] at hx
      exact absurd (hx.unique IsPrimitiveRoot.one) (by norm_num)
    · exact hpos
  · rintro ⟨i, ⟨hi1, hi7⟩, rfl⟩
    refine h.pow_of_coprime i ?_
    interval_cases i <;> decide

/-- The sum of the primitive `7`-th roots of unity equals `μ 7 = -1`. -/
theorem mobius_root_sum_7 :
    ∑ z ∈ primitiveRoots 7 ℂ, z = ((moebius 7 : ℤ) : ℂ) := by
  have h : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 7)) 7 :=
    Complex.isPrimitiveRoot_exp 7 (by norm_num)
  set ζ := Complex.exp (2 * Real.pi * Complex.I / 7)
  rw [primitiveRoots_seven_eq_image h]
  rw [Finset.sum_image (by
    intro i hi j hj hij
    exact h.pow_inj (Finset.mem_Ico.mp hi).2 (Finset.mem_Ico.mp hj).2 hij)]
  have hgeom : ∑ i ∈ Finset.range 7, ζ ^ i = 0 := h.geom_sum_eq_zero (by norm_num)
  have hsplit : ∑ i ∈ Finset.range 7, ζ ^ i = 1 + ∑ i ∈ Finset.Ico 1 7, ζ ^ i := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by norm_num : (0:ℕ) < 7)]
    norm_num
  have hsum : ∑ i ∈ Finset.Ico 1 7, ζ ^ i = -1 := by
    rw [hsplit] at hgeom; linear_combination hgeom
  rw [hsum, moebius_apply_prime (by norm_num)]
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


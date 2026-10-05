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

/-- A fixed primitive 7-th root of unity in `ℂ`. -/
private noncomputable def zeta7 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 7)

private theorem isPrimitiveRoot_zeta7 : IsPrimitiveRoot zeta7 7 :=
  Complex.isPrimitiveRoot_exp 7 (by norm_num)

/-- The primitive 7-th roots of unity are exactly `ζ^k` for `1 ≤ k < 7`. -/
private theorem primitiveRoots_seven_eq :
    primitiveRoots 7 ℂ = (Finset.Ico 1 7).image (fun k => zeta7 ^ k) := by
  have hζ := isPrimitiveRoot_zeta7
  ext x
  simp only [mem_primitiveRoots (by norm_num : 0 < 7), Finset.mem_image, Finset.mem_Ico]
  constructor
  · intro hx
    obtain ⟨i, hi, hix⟩ := hζ.eq_pow_of_pow_eq_one hx.pow_eq_one
    refine ⟨i, ⟨?_, hi⟩, hix⟩
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      simp only [pow_zero] at hix
      exact absurd (hix ▸ hx) (by
        intro h1
        have := h1.unique (IsPrimitiveRoot.one_right_iff.mpr rfl)
        norm_num at this)
    · exact h
  · rintro ⟨k, ⟨hk1, hk7⟩, rfl⟩
    refine hζ.pow_of_coprime k ?_
    interval_cases k <;> decide

theorem mobius_root_sum_7 :
    ∑ z ∈ primitiveRoots 7 ℂ, z = (ArithmeticFunction.moebius 7 : ℂ) := by
  have hζ := isPrimitiveRoot_zeta7
  have hgeom : ∑ i ∈ Finset.range 7, zeta7 ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  have hsplit : ∑ i ∈ Finset.Ico 0 7, zeta7 ^ i
      = zeta7 ^ 0 + ∑ i ∈ Finset.Ico 1 7, zeta7 ^ i :=
    Finset.sum_eq_sum_Ico_succ_bot (by norm_num) _
  rw [Finset.range_eq_Ico] at hgeom
  rw [hsplit, pow_zero] at hgeom
  have hinj : Set.InjOn (fun k => zeta7 ^ k) (Finset.Ico 1 7) := by
    intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    exact hζ.pow_inj (by omega) (by omega) hab
  rw [primitiveRoots_seven_eq, Finset.sum_image (fun a ha b hb h => hinj ha hb h)]
  have : ∑ i ∈ Finset.Ico 1 7, zeta7 ^ i = -1 := by linear_combination hgeom
  rw [this]
  rw [ArithmeticFunction.moebius_apply_prime (by norm_num)]
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


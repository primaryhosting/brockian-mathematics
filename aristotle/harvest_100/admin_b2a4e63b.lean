/-
# Mobius Root Sum 11
Category: Pure Mathematics
Target: Math.mobius_root_sum_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

namespace Math

open Finset

/-- The primitive `11`-th roots of unity in `ℂ` are exactly the powers `ζ ^ k`
for `1 ≤ k ≤ 10`, where `ζ` is any primitive `11`-th root of unity. -/
lemma primitiveRoots_eleven_eq_image {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 11) :
    primitiveRoots 11 ℂ = (Finset.Ico 1 11).image (fun k => ζ ^ k) := by
  ext x
  simp only [mem_primitiveRoots (by norm_num : (0:ℕ) < 11), Finset.mem_image, Finset.mem_Ico]
  constructor
  · intro hx
    obtain ⟨k, hk, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx.pow_eq_one
    refine ⟨k, ⟨?_, hk⟩, rfl⟩
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp only [pow_zero] at hx
      exact absurd rfl (hx.ne_one (by norm_num))
    · exact hpos
  · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
    have hcop : Nat.Coprime k 11 := by interval_cases k <;> decide
    exact hζ.pow_of_coprime k hcop

/-- The sum of the primitive `11`-th roots of unity in `ℂ` equals `μ 11 = -1`. -/
theorem mobius_root_sum_11 :
    ∑ z ∈ primitiveRoots 11 ℂ, z = (ArithmeticFunction.moebius 11 : ℂ) := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 11 :=
    ⟨_, Complex.isPrimitiveRoot_exp 11 (by norm_num)⟩
  have hinj : Set.InjOn (fun k : ℕ => ζ ^ k) (Finset.Ico 1 11) := by
    intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    exact hζ.pow_inj ha.2 hb.2 hab
  have hsum : ∑ z ∈ primitiveRoots 11 ℂ, z = ∑ k ∈ Finset.Ico 1 11, ζ ^ k := by
    rw [primitiveRoots_eleven_eq_image hζ, Finset.sum_image (fun a ha b hb h => hinj ha hb h)]
  have hgeom : ∑ k ∈ Finset.range 11, ζ ^ k = 0 := hζ.geom_sum_eq_zero (by norm_num)
  have hrange : Finset.range 11 = insert 0 (Finset.Ico 1 11) := by decide +kernel
  rw [hrange, Finset.sum_insert (by simp)] at hgeom
  have hmu : (ArithmeticFunction.moebius 11 : ℤ) = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  rw [hsum, hmu]
  push_cast
  simp only [pow_zero] at hgeom
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


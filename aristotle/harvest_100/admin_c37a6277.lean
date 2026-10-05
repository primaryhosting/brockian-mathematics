import Mathlib

/-!
# Mobius Root Sum 7
Category: Pure Mathematics
Target: Math.mobius_root_sum_7
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

set_option grind.warning false

namespace Math

/-- The primitive 7-th roots of unity in `ℂ` are exactly the powers `ζ ^ k`, `1 ≤ k < 7`,
of a fixed primitive 7-th root of unity `ζ`. -/
theorem primitiveRoots_seven_eq_image {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 7) :
    primitiveRoots 7 ℂ = (Finset.Ico 1 7).image (fun k => ζ ^ k) := by
  have hinj : Set.InjOn (fun k => ζ ^ k) (Finset.Ico 1 7 : Finset ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    exact hζ.pow_inj ha.2 hb.2 hab
  have hsub : (Finset.Ico 1 7).image (fun k => ζ ^ k) ⊆ primitiveRoots 7 ℂ := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_Ico] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [mem_primitiveRoots (by norm_num)]
    refine hζ.pow_of_coprime k ?_
    obtain ⟨hk1, hk2⟩ := hk
    interval_cases k <;> decide
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [Finset.card_image_of_injOn hinj, hζ.card_primitiveRoots, Nat.card_Ico]
  decide

/-- The sum of the primitive 7-th roots of unity equals `-1`. -/
theorem sum_primitiveRoots_seven : ∑ z ∈ primitiveRoots 7 ℂ, z = -1 := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 7 :=
    ⟨Complex.exp (2 * Real.pi * Complex.I / 7), Complex.isPrimitiveRoot_exp 7 (by norm_num)⟩
  have hinj : Set.InjOn (fun k => ζ ^ k) (Finset.Ico 1 7 : Finset ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    exact hζ.pow_inj ha.2 hb.2 hab
  rw [primitiveRoots_seven_eq_image hζ,
    Finset.sum_image (fun a ha b hb hab => hinj ha hb hab)]
  have hgeom : ∑ k ∈ Finset.range 7, ζ ^ k = 0 := hζ.geom_sum_eq_zero (by norm_num)
  have hsplit : ∑ k ∈ Finset.range 7, ζ ^ k = 1 + ∑ k ∈ Finset.Ico 1 7, ζ ^ k := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (by norm_num : (0:ℕ) ≤ 1)
      (by norm_num : (1:ℕ) ≤ 7)]
    simp
  rw [hgeom] at hsplit
  linear_combination -hsplit

/-- **Mobius Root Sum 7.**  The sum of the primitive 7-th roots of unity in `ℂ`
equals `μ(7)`, the value of the Möbius function at `7`. -/
theorem mobius_root_sum_7 :
    ∑ z ∈ primitiveRoots 7 ℂ, z = ((ArithmeticFunction.moebius 7 : ℤ) : ℂ) := by
  rw [sum_primitiveRoots_seven,
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7)]
  norm_num

end Math


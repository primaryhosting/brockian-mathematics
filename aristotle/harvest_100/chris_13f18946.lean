import Mathlib

/-!
# Mobius Root Sum 11
Category: Pure Mathematics
Target: Math.mobius_root_sum_11
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

/-- The sum of the primitive `11`-th roots of unity in `ℂ` equals `μ 11 = -1`.

The proof identifies `primitiveRoots 11 ℂ` with `{ζ^i : 1 ≤ i < 11}` for
`ζ = exp(2πi/11)` (using `Complex.isPrimitiveRoot_exp` and
`IsPrimitiveRoot.card_primitiveRoots`), and then uses
`IsPrimitiveRoot.geom_sum_eq_zero` to evaluate the sum as `0 - 1 = -1`. -/
theorem mobius_root_sum_11 :
    ∑ z ∈ primitiveRoots 11 ℂ, z = (ArithmeticFunction.moebius 11 : ℂ) := by
  classical
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 11) with hζdef
  have h : IsPrimitiveRoot ζ 11 := Complex.isPrimitiveRoot_exp 11 (by norm_num)
  have hinjOn : Set.InjOn (fun i : ℕ => ζ ^ i) (Finset.Ico 1 11 : Finset ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    exact h.pow_inj (by omega) (by omega) hab
  have hsub : (Finset.Ico 1 11).image (fun i => ζ ^ i) ⊆ primitiveRoots 11 ℂ := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_Ico] at hx
    obtain ⟨i, ⟨hi1, hi2⟩, rfl⟩ := hx
    rw [mem_primitiveRoots (by norm_num)]
    refine h.pow_of_coprime i ?_
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 (by omega)
  have himg : ((Finset.Ico 1 11).image (fun i => ζ ^ i)).card = 10 := by
    rw [Finset.card_image_of_injOn hinjOn]; simp
  have hcard : (primitiveRoots 11 ℂ).card = 10 := by
    rw [h.card_primitiveRoots]; decide
  have heq : (Finset.Ico 1 11).image (fun i => ζ ^ i) = primitiveRoots 11 ℂ :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, himg])
  have hgeom : ∑ i ∈ Finset.range 11, ζ ^ i = 0 := h.geom_sum_eq_zero (by norm_num)
  have hrange : Finset.range 11 = insert 0 (Finset.Ico 1 11) := by decide
  rw [hrange, Finset.sum_insert (by simp), pow_zero] at hgeom
  rw [← heq, Finset.sum_image
    (fun a ha b hb hab => hinjOn (by simpa using ha) (by simpa using hb) hab)]
  have hIco : ∑ i ∈ Finset.Ico 1 11, ζ ^ i = -1 := by linear_combination hgeom
  rw [hIco]
  norm_num [ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 11)]

end Math


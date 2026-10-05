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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

open Polynomial Finset

/-- The primitive 7-th roots of unity in `ℂ` are exactly the powers `ζ^i`, `1 ≤ i < 7`,
of a fixed primitive 7-th root `ζ`. -/
theorem primitiveRoots_seven_eq_image {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 7) :
    primitiveRoots 7 ℂ = (Finset.Ico 1 7).image (fun i => ζ ^ i) := by
  ext x
  simp only [mem_primitiveRoots (by norm_num : (0:ℕ) < 7), Finset.mem_image, Finset.mem_Ico]
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx.pow_eq_one
    refine ⟨i, ⟨?_, hi⟩, rfl⟩
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      simp only [pow_zero] at hx
      simpa using hx.unique (IsPrimitiveRoot.one (M := ℂ))
    · exact h
  · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
    have hcop : Nat.Coprime i 7 := by
      have hp : Nat.Prime 7 := by norm_num
      have h7 : ¬ (7 ∣ i) := by omega
      exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr h7).symm
    exact hζ.pow_of_coprime i hcop

theorem mobius_root_sum_7 :
    ∑ z ∈ primitiveRoots 7 ℂ, z = (ArithmeticFunction.moebius 7 : ℂ) := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 7 :=
    ⟨Complex.exp (2 * Real.pi * Complex.I / 7), Complex.isPrimitiveRoot_exp 7 (by norm_num)⟩
  rw [primitiveRoots_seven_eq_image hζ, Finset.sum_image]
  · have h0 : ∑ i ∈ Finset.range 7, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
    have : Finset.range 7 = insert 0 (Finset.Ico 1 7) := by decide
    rw [this, Finset.sum_insert (by decide)] at h0
    have hm : (ArithmeticFunction.moebius 7 : ℤ) = -1 := by
      simpa using ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7)
    rw [hm]
    push_cast
    linear_combination h0 - (pow_zero ζ)
  · intro i hi j hj h
    simp only [Finset.coe_Ico, Set.mem_Ico] at hi hj
    exact hζ.pow_inj (by omega) (by omega) h

end Math


import Mathlib

/-!
# Mobius Root Sum 7
Category: Pure Mathematics
Target: Math.mobius_root_sum_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Polynomial

namespace Math

/-- The primitive `7`-th roots of unity in `ℂ` are exactly the powers `ζ^i`, `1 ≤ i < 7`,
of `ζ = exp(2πi/7)`. -/
lemma primitiveRoots_seven_eq_image {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 7) :
    primitiveRoots 7 ℂ = (Finset.Ico 1 7).image (fun i => ζ ^ i) := by
  ext z
  simp only [mem_primitiveRoots (by norm_num : (0:ℕ) < 7), Finset.mem_image, Finset.mem_Ico]
  constructor
  · intro hz
    obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz.pow_eq_one
    refine ⟨i, ⟨?_, hi⟩, rfl⟩
    rcases Nat.eq_zero_or_pos i with rfl | h
    · simp only [pow_zero] at hz
      have := hz.unique IsPrimitiveRoot.one
      omega
    · exact h
  · rintro ⟨i, ⟨hi1, hi7⟩, rfl⟩
    have hcop : Nat.Coprime i 7 := by
      have hp : Nat.Prime 7 := by norm_num
      rw [Nat.coprime_comm]
      exact (Nat.Prime.coprime_iff_not_dvd hp).2 (fun hd => by
        have := Nat.le_of_dvd (by omega) hd; omega)
    exact hζ.pow_of_coprime i hcop

/-- The sum of the primitive `7`-th roots of unity equals `μ(7) = -1`. -/
theorem mobius_root_sum_7 :
    ∑ z ∈ primitiveRoots 7 ℂ, z = (ArithmeticFunction.moebius 7 : ℂ) := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 7 :=
    ⟨Complex.exp (2 * Real.pi * Complex.I / 7), Complex.isPrimitiveRoot_exp 7 (by norm_num)⟩
  have hinj : Set.InjOn (fun i => ζ ^ i) (Finset.Ico 1 7 : Finset ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    exact hζ.pow_inj (by omega) (by omega) hab
  have hsum : ∑ i ∈ Finset.range 7, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  rw [primitiveRoots_seven_eq_image hζ, Finset.sum_image hinj]
  have h1 : Finset.range 7 = insert 0 (Finset.Ico 1 7) := by decide
  rw [h1, Finset.sum_insert (by simp)] at hsum
  have hmu : (ArithmeticFunction.moebius 7 : ℂ) = -1 := by
    have : ArithmeticFunction.moebius 7 = -1 := by
      rw [ArithmeticFunction.moebius_apply_prime (by norm_num)]
    rw [this]; norm_num
  rw [hmu]
  simp only [pow_zero] at hsum
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


/-
# Mobius Root Sum 11
Category: Pure Mathematics
Target: Math.mobius_root_sum_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` before any module docstring, so the header above is
-- repeated verbatim as a module docstring immediately after the import.)
import Mathlib

/-!
# Mobius Root Sum 11
Category: Pure Mathematics
Target: Math.mobius_root_sum_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Finset

namespace Math

/-- The primitive `11`-th roots of unity in `ℂ` are exactly the powers `ζ ^ i`,
`1 ≤ i < 11`, of the standard primitive root `ζ = exp (2 π i / 11)`. -/
theorem primitiveRoots_eleven_eq_image {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 11) :
    primitiveRoots 11 ℂ = (Finset.Ico 1 11).image (fun i => ζ ^ i) := by
  ext η
  simp only [Finset.mem_image, Finset.mem_Ico, mem_primitiveRoots (by norm_num : 0 < 11)]
  constructor
  · intro hη
    obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη.pow_eq_one
    refine ⟨i, ⟨?_, hi⟩, rfl⟩
    rcases Nat.eq_zero_or_pos i with rfl | h
    · simp only [pow_zero] at hη
      exact absurd (hη.unique IsPrimitiveRoot.one) (by norm_num)
    · exact h
  · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
    have hcop : Nat.Coprime i 11 := by
      have hp : Nat.Prime 11 := by norm_num
      rw [Nat.coprime_comm]
      refine (Nat.Prime.coprime_iff_not_dvd hp).2 ?_
      intro hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    exact hζ.pow_of_coprime i hcop

/-- The sum of the primitive `11`-th roots of unity equals `μ 11`. -/
theorem mobius_root_sum_11 :
    ∑ ζ ∈ primitiveRoots 11 ℂ, ζ = (ArithmeticFunction.moebius 11 : ℂ) := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 11 :=
    ⟨Complex.exp (2 * Real.pi * Complex.I / 11), Complex.isPrimitiveRoot_exp 11 (by norm_num)⟩
  have hinj : Set.InjOn (fun i => ζ ^ i) (Finset.Ico 1 11 : Finset ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    exact hζ.pow_inj (by omega) (by omega) hab
  rw [primitiveRoots_eleven_eq_image hζ, Finset.sum_image (by
    intro a ha b hb hab; exact hinj ha hb hab)]
  have hgeom : ∑ i ∈ Finset.range 11, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  have hsplit : ∑ i ∈ Finset.range 11, ζ ^ i
      = ζ ^ 0 + ∑ i ∈ Finset.Ico 1 11, ζ ^ i := by
    rw [Finset.range_eq_Ico, ← Finset.sum_eq_sum_Ico_succ_bot (by norm_num)]
  have hmu : (ArithmeticFunction.moebius 11 : ℂ) = -1 := by
    rw [ArithmeticFunction.moebius_apply_prime (by norm_num)]
    norm_num
  rw [hmu]
  rw [hsplit] at hgeom
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


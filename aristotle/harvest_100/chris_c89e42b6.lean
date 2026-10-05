/-
# Mobius Root Sum 7
Category: Pure Mathematics
Target: Math.mobius_root_sum_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is written as a plain block comment.)

import Mathlib

open Finset Complex

namespace Math

/-- The set of primitive `7`-th roots of unity in `ℂ` is exactly the set of powers
`ζ ^ i` for `1 ≤ i < 7`, where `ζ = exp (2πi/7)`. -/
lemma primitiveRoots_seven_eq_image {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 7) :
    primitiveRoots 7 ℂ = (Finset.Ico 1 7).image (fun i => ζ ^ i) := by
  ext x
  simp only [mem_primitiveRoots (by norm_num : (0:ℕ) < 7), Finset.mem_image, Finset.mem_Ico]
  constructor
  · intro hx
    rw [hζ.isPrimitiveRoot_iff] at hx
    obtain ⟨i, hi7, hic, hix⟩ := hx
    refine ⟨i, ⟨?_, hi7⟩, hix⟩
    rcases Nat.eq_zero_or_pos i with rfl | h
    · simp [Nat.Coprime] at hic
    · exact h
  · rintro ⟨i, ⟨hi1, hi7⟩, rfl⟩
    refine hζ.pow_of_coprime i ?_
    interval_cases i <;> decide

/-- The sum of the primitive 7-th roots of unity in `ℂ` equals `μ 7 = -1`. -/
theorem mobius_root_sum_7 :
    ∑ z ∈ primitiveRoots 7 ℂ, z = (ArithmeticFunction.moebius 7 : ℂ) := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 7 :=
    ⟨Complex.exp (2 * Real.pi * Complex.I / 7), Complex.isPrimitiveRoot_exp 7 (by norm_num)⟩
  rw [primitiveRoots_seven_eq_image hζ,
    Finset.sum_image (fun i hi j hj h => hζ.pow_inj (by simpa using (Finset.mem_Ico.1 hi).2)
      (by simpa using (Finset.mem_Ico.1 hj).2) h)]
  have hgeom : ∑ i ∈ Finset.range 7, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  have hsplit : ∑ i ∈ Finset.range 7, ζ ^ i = 1 + ∑ i ∈ Finset.Ico 1 7, ζ ^ i := by
    rw [Finset.range_eq_Ico,
      Finset.sum_eq_sum_Ico_succ_bot (by norm_num : (0:ℕ) < 7) (fun i => ζ ^ i)]
    simp
  have h1 : ∑ i ∈ Finset.Ico 1 7, ζ ^ i = -1 := by
    have := hsplit.symm.trans hgeom
    linear_combination this
  rw [h1]
  have : ArithmeticFunction.moebius 7 = -1 := by
    rw [ArithmeticFunction.moebius_apply_prime (by norm_num)]
  rw [this]
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


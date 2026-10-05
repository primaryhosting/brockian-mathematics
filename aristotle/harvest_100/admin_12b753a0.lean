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

open scoped ArithmeticFunction

/-- The Möbius function at `5` is `-1`. -/
lemma moebius_five : (ArithmeticFunction.moebius 5 : ℤ) = -1 := by
  have h : Nat.Prime 5 := by norm_num
  simpa using ArithmeticFunction.moebius_apply_prime h

/-- A fixed primitive 5-th root of unity in `ℂ`. -/
noncomputable def zeta5 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

lemma isPrimitiveRoot_zeta5 : IsPrimitiveRoot zeta5 5 :=
  Complex.isPrimitiveRoot_exp 5 (by norm_num)

/-- The primitive 5-th roots of unity are exactly the powers `ζ^i` with `1 ≤ i < 5`. -/
lemma primitiveRoots_five_eq_image :
    primitiveRoots 5 ℂ = (Finset.Ico 1 5).image (fun i => zeta5 ^ i) := by
  have hζ := isPrimitiveRoot_zeta5
  ext x
  simp only [Finset.mem_image, Finset.mem_Ico, mem_primitiveRoots (by norm_num : 0 < 5)]
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx.pow_eq_one
    refine ⟨i, ⟨?_, hi⟩, rfl⟩
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · exact absurd (by simpa [h0] using hx) (by simpa using fun h => (h.ne_one (by norm_num)) rfl)
    · exact h0
  · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
    refine hζ.pow_of_coprime i ?_
    interval_cases i <;> decide

/-- The sum of the primitive 5-th roots of unity equals `μ(5)`. -/
theorem mobius_root_sum_5 :
    ∑ x ∈ primitiveRoots 5 ℂ, x = (ArithmeticFunction.moebius 5 : ℂ) := by
  have hζ := isPrimitiveRoot_zeta5
  have hinj : Set.InjOn (fun i => zeta5 ^ i) (Finset.Ico 1 5 : Finset ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_Ico, Set.mem_Ico] at hi hj
    exact hζ.pow_inj hi.2 hj.2 hij
  have hgeom : ∑ i ∈ Finset.range 5, zeta5 ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  have hsplit : ∑ i ∈ Finset.range 5, zeta5 ^ i
      = 1 + ∑ i ∈ Finset.Ico 1 5, zeta5 ^ i := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by norm_num : (0:ℕ) < 5)]
    norm_num
  rw [primitiveRoots_five_eq_image, Finset.sum_image (fun i hi j hj h => hinj hi hj h)]
  have : ∑ i ∈ Finset.Ico 1 5, zeta5 ^ i = -1 := by
    have := hsplit ▸ hgeom
    linear_combination this
  rw [this]
  have : (ArithmeticFunction.moebius 5 : ℤ) = -1 := moebius_five
  push_cast [this]
  ring

end Math


/-
# Mobius Root Sum 11
Category: Pure Mathematics
Target: Math.mobius_root_sum_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 11
Category: Pure Mathematics
Target: Math.mobius_root_sum_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- For a primitive `p`-th root of unity `ζ` with `p` prime, the primitive `p`-th roots of
unity are exactly the powers `ζ ^ i` with `1 ≤ i < p`. -/
lemma primitiveRoots_eq_image_of_prime {p : ℕ} (hp : p.Prime) {ζ : ℂ}
    (h : IsPrimitiveRoot ζ p) :
    primitiveRoots p ℂ = (Finset.Ico 1 p).image (fun i => ζ ^ i) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  ext x
  simp only [Finset.mem_image, Finset.mem_Ico, mem_primitiveRoots hp.pos]
  constructor
  · intro hx
    obtain ⟨i, hi, hix⟩ := h.eq_pow_of_pow_eq_one hx.pow_eq_one
    refine ⟨i, ⟨?_, hi⟩, hix⟩
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exfalso
      simp only [pow_zero] at hix
      exact hx.pow_ne_one_of_pos_of_lt one_ne_zero hp.one_lt (by simp [← hix])
    · exact hpos
  · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
    refine h.pow_of_coprime i (Nat.Coprime.symm ((hp.coprime_iff_not_dvd).mpr ?_))
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega

/-- The sum of the primitive 11-th roots of unity in `ℂ` equals `μ 11 = -1`. -/
theorem mobius_root_sum_11 :
    ∑ z ∈ primitiveRoots 11 ℂ, z = (ArithmeticFunction.moebius 11 : ℂ) := by
  have hp : Nat.Prime 11 := by norm_num
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 11) with hζdef
  have h : IsPrimitiveRoot ζ 11 := Complex.isPrimitiveRoot_exp 11 (by norm_num)
  have hinj : Set.InjOn (fun i => ζ ^ i) (Finset.Ico 1 11) := by
    intro i hi j hj hij
    simp only [Finset.coe_Ico, Set.mem_Ico] at hi hj
    exact h.pow_inj (by omega) (by omega) hij
  rw [primitiveRoots_eq_image_of_prime hp h, Finset.sum_image (fun i hi j hj hij =>
    hinj (by simpa using hi) (by simpa using hj) hij)]
  have hgeom : ∑ i ∈ Finset.range 11, ζ ^ i = 0 := h.geom_sum_eq_zero (by norm_num)
  have hsplit : ∑ i ∈ Finset.range 11, ζ ^ i = 1 + ∑ i ∈ Finset.Ico 1 11, ζ ^ i := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive (fun i => ζ ^ i) (Nat.zero_le 1) (by norm_num : (1:ℕ) ≤ 11)]
    simp
  have : (1 : ℂ) + ∑ i ∈ Finset.Ico 1 11, ζ ^ i = 0 := by rw [← hsplit, hgeom]
  rw [ArithmeticFunction.moebius_apply_prime hp]
  push_cast
  linear_combination this

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


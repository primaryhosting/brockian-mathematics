/-
# Mobius Root Sum 11
Category: Pure Mathematics
Target: Math.mobius_root_sum_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset Polynomial

namespace Math

/-- The primitive `11`-th roots of unity in `ℂ` are exactly the powers `ζ ^ i`
for `1 ≤ i < 11`, where `ζ` is any primitive `11`-th root of unity. -/
theorem sum_primitiveRoots_eleven_eq (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 11) :
    ∑ z ∈ primitiveRoots 11 ℂ, z = ∑ i ∈ Finset.Ico 1 11, ζ ^ i := by
  have hp : Nat.Prime 11 := by norm_num
  refine (Finset.sum_bij (fun i _ => ζ ^ i) ?_ ?_ ?_ ?_).symm
  · intro i hi
    simp only [Finset.mem_Ico] at hi
    rw [mem_primitiveRoots (by norm_num)]
    have hc : Nat.Coprime i 11 := by
      refine Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun hdvd => ?_)
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    exact hζ.pow_of_coprime i hc
  · intro i hi j hj hij
    simp only [Finset.mem_Ico] at hi hj
    exact hζ.pow_inj (by omega) (by omega) hij
  · intro x hx
    rw [mem_primitiveRoots (by norm_num), hζ.isPrimitiveRoot_iff] at hx
    obtain ⟨i, hi_lt, hi_cop, rfl⟩ := hx
    refine ⟨i, ?_, rfl⟩
    simp only [Finset.mem_Ico]
    refine ⟨?_, hi_lt⟩
    rcases Nat.eq_zero_or_pos i with rfl | h
    · simp [Nat.coprime_zero_left] at hi_cop
    · exact h
  · intro i _
    rfl

/-- The sum of the primitive `11`-th roots of unity in `ℂ` equals `μ 11 = -1`. -/
theorem mobius_root_sum_11 :
    ∑ z ∈ primitiveRoots 11 ℂ, z = (ArithmeticFunction.moebius 11 : ℂ) := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 11 :=
    ⟨Complex.exp (2 * Real.pi * Complex.I / 11), Complex.isPrimitiveRoot_exp 11 (by norm_num)⟩
  rw [sum_primitiveRoots_eleven_eq ζ hζ]
  have hgeom : ∑ i ∈ Finset.range 11, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  have hsplit : ∑ i ∈ Finset.range 11, ζ ^ i = 1 + ∑ i ∈ Finset.Ico 1 11, ζ ^ i := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive (fun i => ζ ^ i) (Nat.zero_le 1) (by norm_num : (1:ℕ) ≤ 11)]
    simp
  have hmu : (ArithmeticFunction.moebius 11 : ℤ) = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  have hz : (1 : ℂ) + ∑ i ∈ Finset.Ico 1 11, ζ ^ i = 0 := by rw [← hsplit, hgeom]
  rw [hmu]
  push_cast
  linear_combination hz

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


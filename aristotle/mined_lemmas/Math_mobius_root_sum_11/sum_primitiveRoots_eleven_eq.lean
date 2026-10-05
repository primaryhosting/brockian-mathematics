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

/-
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- The Möbius function at `6` equals `1` (since `6 = 2 * 3` is squarefree with two prime
factors). -/

theorem primitiveRoots_six_eq {z : ℂ} (h : IsPrimitiveRoot z 6) :
    primitiveRoots 6 ℂ = {z, z ^ 5} := by
  have hz2 : z ^ 2 - z + 1 = 0 := cyclotomic_six_eq_zero_of_isPrimitiveRoot h
  have hne : z ≠ z ^ 5 := by
    intro he
    have h1 : 2 * z - 1 = 0 := by linear_combination he + (z ^ 3 + z ^ 2 - 1) * hz2
    have h3 : (3 : ℂ) = 0 := by linear_combination 4 * hz2 - (2 * z - 1) * h1
    norm_num at h3
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (mem_primitiveRoots (by norm_num)).2 h
    · exact (mem_primitiveRoots (by norm_num)).2 (h.pow_of_coprime 5 (by norm_num))
  · rw [h.card_primitiveRoots, show Nat.totient 6 = 2 from by decide +kernel,
      Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]

/-- **The sum of the primitive 6-th roots of unity equals `μ(6)`.** -/

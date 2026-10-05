/-
# Mobius Root Sum 8
Category: Pure Mathematics
Target: Math.mobius_root_sum_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

/-- A fixed primitive `8`-th root of unity in `ℂ`. -/

theorem primitiveRoots_eight :
    primitiveRoots 8 ℂ = {zeta8, zeta8 ^ 3, zeta8 ^ 5, zeta8 ^ 7} := by
  have hsub : ({zeta8, zeta8 ^ 3, zeta8 ^ 5, zeta8 ^ 7} : Finset ℂ) ⊆ primitiveRoots 8 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [mem_primitiveRoots (by norm_num)]
    rcases hx with h | h | h | h <;> subst h
    · exact isPrimitiveRoot_zeta8
    · exact isPrimitiveRoot_zeta8.pow_of_coprime 3 (by decide)
    · exact isPrimitiveRoot_zeta8.pow_of_coprime 5 (by decide)
    · exact isPrimitiveRoot_zeta8.pow_of_coprime 7 (by decide)
  have h1 := zeta8_pow_ne 1 3 (by norm_num) (by norm_num) (by norm_num)
  have h2 := zeta8_pow_ne 1 5 (by norm_num) (by norm_num) (by norm_num)
  have h3 := zeta8_pow_ne 1 7 (by norm_num) (by norm_num) (by norm_num)
  have h4 := zeta8_pow_ne 3 5 (by norm_num) (by norm_num) (by norm_num)
  have h5 := zeta8_pow_ne 3 7 (by norm_num) (by norm_num) (by norm_num)
  have h6 := zeta8_pow_ne 5 7 (by norm_num) (by norm_num) (by norm_num)
  simp only [pow_one] at h1 h2 h3
  have hcard : #({zeta8, zeta8 ^ 3, zeta8 ^ 5, zeta8 ^ 7} : Finset ℂ) = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h1, h2, h3]),
      Finset.card_insert_of_notMem (by simp [h4, h5]),
      Finset.card_insert_of_notMem (by simp [h6]), Finset.card_singleton]
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [hcard, Complex.card_primitiveRoots]
  decide


import RequestProject.Mertens

/-!
# The main term: `∏_{3 ≤ p ≤ z} (1 - 2/p) ≤ 16 / (log z)^2`

This is proved by the elementary Euler-type argument: expanding `∏ (1 + 1/(p-1))` over
subsets dominates `∑_{a ≤ z squarefree} 1/a`, which in turn is at least half the harmonic
sum, hence at least `(log z)/2`.
-/

namespace Brun

open Finset


lemma prod_oddPrimes_le (z : ℕ) (hz : 2 ≤ z) :
    ∏ p ∈ oddPrimes z, (1 - 2 / (p : ℝ)) ≤ 16 / (Real.log z) ^ 2 := by
  have hlog : 0 < Real.log z := Real.log_pos (by exact_mod_cast hz)
  have hins : primesLE z = insert 2 (oddPrimes z) := by
    ext p
    simp only [mem_primesLE, Finset.mem_insert, mem_oddPrimes]
    constructor
    · rintro ⟨hpz, hp⟩
      by_cases h2 : p = 2
      · exact Or.inl h2
      · exact Or.inr ⟨hpz, hp, h2⟩
    · rintro (rfl | ⟨hpz, hp, -⟩)
      · exact ⟨hz, Nat.prime_two⟩
      · exact ⟨hpz, hp⟩
  have h2mem : (2:ℕ) ∉ oddPrimes z := by
    simp [mem_oddPrimes]
  have hsplit : ∏ p ∈ primesLE z, (1 - 1 / (p : ℝ))
      = (1/2) * ∏ p ∈ oddPrimes z, (1 - 1 / (p : ℝ)) := by
    rw [hins, Finset.prod_insert h2mem]
    norm_num
  have hle : ∏ p ∈ oddPrimes z, (1 - 2 / (p : ℝ))
      ≤ ∏ p ∈ oddPrimes z, (1 - 1 / (p : ℝ)) ^ 2 := by
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have := three_le_of_mem_oddPrimes hp
      have h3 : (3:ℝ) ≤ p := by exact_mod_cast this
      rw [sub_nonneg, div_le_one (by linarith)]
      linarith
    · have := three_le_of_mem_oddPrimes hp
      have h3 : (3:ℝ) ≤ p := by exact_mod_cast this
      have hp0 : (0:ℝ) < p := by linarith
      rw [div_add_div_same, sub_sq]
      have : (1 / (p:ℝ)) ^ 2 ≥ 0 := by positivity
      have hh : 2 * 1 * (1 / (p:ℝ)) = 2 / p := by ring
      nlinarith [this]
  have hnn : 0 ≤ ∏ p ∈ oddPrimes z, (1 - 1 / (p : ℝ)) := by
    refine Finset.prod_nonneg (fun p hp => ?_)
    have := three_le_of_mem_oddPrimes hp
    have h3 : (3:ℝ) ≤ p := by exact_mod_cast this
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  have hkey : ∏ p ∈ oddPrimes z, (1 - 1 / (p : ℝ)) ≤ 4 / Real.log z := by
    have := prod_one_sub_inv_le z hz
    rw [hsplit] at this
    linarith
  calc ∏ p ∈ oddPrimes z, (1 - 2 / (p : ℝ))
      ≤ ∏ p ∈ oddPrimes z, (1 - 1 / (p : ℝ)) ^ 2 := hle
  _ = (∏ p ∈ oddPrimes z, (1 - 1 / (p : ℝ))) ^ 2 := by rw [Finset.prod_pow]
  _ ≤ (4 / Real.log z) ^ 2 := by
        apply pow_le_pow_left hnn hkey
  _ = 16 / (Real.log z) ^ 2 := by
        rw [div_pow]; norm_num

end Brun

import Mathlib

/-!
# Basic definitions for Brun's theorem on twin primes
-/

namespace Brun

open Finset

/-- The set of odd primes `≤ z`. -/

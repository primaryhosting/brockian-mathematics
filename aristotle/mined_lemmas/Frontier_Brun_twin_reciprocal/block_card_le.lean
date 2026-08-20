import RequestProject.Mertens

/-!
# The main term: `∏_{3 ≤ p ≤ z} (1 - 2/p) ≤ 16 / (log z)^2`

This is proved by the elementary Euler-type argument: expanding `∏ (1 + 1/(p-1))` over
subsets dominates `∑_{a ≤ z squarefree} 1/a`, which in turn is at least half the harmonic
sum, hence at least `(log z)/2`.
-/

namespace Brun

open Finset


lemma block_card_le (i : ℕ) : i * (block i).card ≤ 2 ^ (i + 2) := by
  have h1 : (2 ^ i) ^ (block i).card ≤ ∏ p ∈ block i, p := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod' ?_
    intro p hp
    exact le_of_lt (Finset.mem_filter.mp hp).2
  have h2 : ∏ p ∈ block i, p ≤ ∏ p ∈ primesLE (2 ^ (i + 1)), p := by
    refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
    intro p hp _
    exact (mem_primesLE.mp hp).2.one_lt.le
  have h3 : ∏ p ∈ primesLE (2 ^ (i + 1)), p ≤ 4 ^ (2 ^ (i + 1)) := prod_primesLE_le _
  have h4 : (2:ℕ) ^ (i * (block i).card) ≤ 2 ^ (2 ^ (i + 2)) := by
    calc (2:ℕ) ^ (i * (block i).card) = (2 ^ i) ^ (block i).card := by rw [pow_mul]
    _ ≤ 4 ^ (2 ^ (i + 1)) := le_trans h1 (le_trans h2 h3)
    _ = 2 ^ (2 ^ (i + 2)) := by
        rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
        ring_nf
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h4


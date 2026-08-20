import RequestProject.Mertens

/-!
# The main term: `∏_{3 ≤ p ≤ z} (1 - 2/p) ≤ 16 / (log z)^2`

This is proved by the elementary Euler-type argument: expanding `∏ (1 + 1/(p-1))` over
subsets dominates `∑_{a ≤ z squarefree} 1/a`, which in turn is at least half the harmonic
sum, hence at least `(log z)/2`.
-/

namespace Brun

open Finset


lemma sum_inv_block_le (i : ℕ) (hi : 1 ≤ i) :
    ∑ p ∈ block i, (1 / p : ℝ) ≤ 4 / i := by
  have hcard : ((block i).card : ℝ) ≤ 2 ^ (i + 2) / i := by
    have := block_card_le i
    rw [le_div_iff₀ (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hi)]
    calc ((block i).card : ℝ) * i = ((i * (block i).card : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((2 ^ (i + 2) : ℕ) : ℝ) := by exact_mod_cast this
    _ = 2 ^ (i + 2) := by push_cast; ring
  have hstep : ∀ p ∈ block i, (1 / p : ℝ) ≤ 1 / 2 ^ i := by
    intro p hp
    have hp' : (2:ℝ) ^ i < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
    have : (0:ℝ) < 2 ^ i := by positivity
    exact one_div_le_one_div_of_le this hp'.le
  calc ∑ p ∈ block i, (1 / p : ℝ) ≤ ∑ _p ∈ block i, (1 / 2 ^ i : ℝ) :=
        Finset.sum_le_sum hstep
  _ = (block i).card * (1 / 2 ^ i) := by rw [Finset.sum_const, nsmul_eq_mul]
  _ ≤ (2 ^ (i + 2) / i) * (1 / 2 ^ i) := by gcongr
  _ = 4 / i := by
        rw [pow_add]
        field_simp
        ring


import RequestProject.Mertens

/-!
# The main term: `∏_{3 ≤ p ≤ z} (1 - 2/p) ≤ 16 / (log z)^2`

This is proved by the elementary Euler-type argument: expanding `∏ (1 + 1/(p-1))` over
subsets dominates `∑_{a ≤ z squarefree} 1/a`, which in turn is at least half the harmonic
sum, hence at least `(log z)/2`.
-/

namespace Brun

open Finset


lemma sum_inv_primesLE_pow_le (J : ℕ) :
    ∑ p ∈ primesLE (2 ^ J), (1 / p : ℝ) ≤ 1 / 2 + ∑ i ∈ Ico 1 J, (4 / i : ℝ) := by
  induction J with
  | zero =>
    have h : primesLE (2 ^ 0) = ∅ := by
      ext p
      simp only [mem_primesLE, pow_zero, Finset.notMem_empty, iff_false, not_and]
      intro hp hpp
      have := hpp.two_le
      omega
    rw [h]; simp
  | succ J ih =>
    rcases Nat.eq_zero_or_pos J with rfl | hJ
    · have h : primesLE (2 ^ (0 + 1)) = {2} := by
        ext p
        simp only [mem_primesLE, Finset.mem_singleton, zero_add, pow_one]
        constructor
        · rintro ⟨hp, hpp⟩; have := hpp.two_le; omega
        · rintro rfl; exact ⟨le_rfl, Nat.prime_two⟩
      rw [h]; norm_num
    · have hsplit : ∑ p ∈ primesLE (2 ^ (J + 1)), (1 / p : ℝ)
          = ∑ p ∈ primesLE (2 ^ J), (1 / p : ℝ) + ∑ p ∈ block J, (1 / p : ℝ) := by
        rw [← Finset.sum_filter_add_sum_filter_not (primesLE (2 ^ (J + 1)))
          (fun p => p ≤ 2 ^ J)]
        congr 1
        · congr 1
          ext p
          simp only [Finset.mem_filter, mem_primesLE]
          constructor
          · rintro ⟨⟨-, hp⟩, hle⟩; exact ⟨hle, hp⟩
          · rintro ⟨hle, hp⟩
            exact ⟨⟨hle.trans (Nat.pow_le_pow_right (by norm_num) (by omega)), hp⟩, hle⟩
        · congr 1
          ext p
          simp only [Finset.mem_filter, block, not_le]
      rw [hsplit, Finset.sum_Ico_succ_top (by omega)]
      have := sum_inv_block_le J hJ
      linarith [ih]


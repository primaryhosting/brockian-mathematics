import RequestProject.Mertens

/-!
# The main term: `∏_{3 ≤ p ≤ z} (1 - 2/p) ≤ 16 / (log z)^2`

This is proved by the elementary Euler-type argument: expanding `∏ (1 + 1/(p-1))` over
subsets dominates `∑_{a ≤ z squarefree} 1/a`, which in turn is at least half the harmonic
sum, hence at least `(log z)/2`.
-/

namespace Brun

open Finset

def oddPrimes (z : ℕ) : Finset ℕ := (range (z + 1)).filter (fun p => p.Prime ∧ p ≠ 2)

/-- The number of odd `n < N` such that every prime in `s` divides `n * (n + 2)`. -/

lemma mem_oddPrimes {z p : ℕ} : p ∈ oddPrimes z ↔ p ≤ z ∧ p.Prime ∧ p ≠ 2 := by
  simp [oddPrimes, Nat.lt_succ_iff, and_assoc]

def primesLE (x : ℕ) : Finset ℕ := (range (x + 1)).filter Nat.Prime

lemma mem_primesLE {x p : ℕ} : p ∈ primesLE x ↔ p ≤ x ∧ p.Prime := by
  simp [primesLE, Nat.lt_succ_iff]

lemma prod_primesLE_le (x : ℕ) : ∏ p ∈ primesLE x, p ≤ 4 ^ x := primorial_le_4_pow x

/-- The primes in `(2^i, 2^(i+1)]`. -/

def block (i : ℕ) : Finset ℕ := (primesLE (2 ^ (i + 1))).filter (fun p => 2 ^ i < p)

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

lemma sum_inv_le_two_sqrt (J : ℕ) : ∑ i ∈ Icc 1 J, (1 / i : ℝ) ≤ 2 * Real.sqrt J := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have ha : Real.sqrt J ^ 2 = J := Real.sq_sqrt (by positivity)
    have hb : Real.sqrt (J + 1) ^ 2 = (J : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hab : Real.sqrt J ≤ Real.sqrt (J + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    have hb1 : 1 ≤ Real.sqrt (J + 1) := by
      have h1 : Real.sqrt 1 ≤ Real.sqrt ((J : ℝ) + 1) :=
        Real.sqrt_le_sqrt (by linarith [(Nat.cast_nonneg J : (0:ℝ) ≤ J)])
      simpa using h1
    have key : 1 / ((J : ℝ) + 1) ≤ 2 * Real.sqrt (J + 1) - 2 * Real.sqrt J := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.sqrt_nonneg (J:ℝ), Real.sqrt_nonneg ((J:ℝ)+1)]
    push_cast
    push_cast at ih
    linarith

/-- The Mertens-type bound we need: the sum of `2/p` over odd primes `p ≤ 2^J`. -/

lemma sum_two_div_oddPrimes_le (J : ℕ) :
    ∑ p ∈ oddPrimes (2 ^ J), (2 / p : ℝ) ≤ 1 + 16 * Real.sqrt J := by
  have hsub : oddPrimes (2 ^ J) ⊆ primesLE (2 ^ J) := by
    intro p hp
    rw [mem_oddPrimes] at hp
    exact mem_primesLE.mpr ⟨hp.1, hp.2.1⟩
  have h1 : ∑ p ∈ oddPrimes (2 ^ J), (2 / p : ℝ) ≤ ∑ p ∈ primesLE (2 ^ J), (2 / p : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro p _ _
    positivity
  have h2 : ∑ p ∈ primesLE (2 ^ J), (2 / p : ℝ) = 2 * ∑ p ∈ primesLE (2 ^ J), (1 / p : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  have h3 := sum_inv_primesLE_pow_le J
  have h4 : ∑ i ∈ Ico 1 J, (4 / i : ℝ) ≤ 8 * Real.sqrt J := by
    have : ∑ i ∈ Ico 1 J, (4 / i : ℝ) ≤ ∑ i ∈ Icc 1 J, (4 / i : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
      exact Finset.Ico_subset_Icc_self
    have h5 : ∑ i ∈ Icc 1 J, (4 / i : ℝ) = 4 * ∑ i ∈ Icc 1 J, (1 / i : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have := sum_inv_le_two_sqrt J
    linarith
  linarith

end Brun

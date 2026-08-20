import Mathlib
namespace Brockian.SylvesterSchur

/-!
# The Sylvester–Schur theorem

If `n > k ≥ 1` then one of `n+1, …, n+k` has a prime factor `> k`.

The proof follows Erdős' argument: assuming the contrary, every prime factor of the
binomial coefficient `(n+k).choose k` is at most `k`.  This yields two upper bounds for
that binomial coefficient (one via the number of primes `≤ k`, one via the primorial),
both of which are contradicted by an elementary lower bound, except in a range of small
parameters which is covered by an explicit chain of primes.
-/

open Finset Real

/-! ### An elementary upper bound for the prime counting function -/

/-- The number of primes `≤ k`. -/

theorem sylvester_schur (n k : ℕ) (h : k < n) (hk : 0 < k) :
    ∃ i ∈ Finset.range k, ∃ p, p.Prime ∧ k < p ∧ p ∣ (n + 1 + i) := by
  by_contra hcon0
  have hcon : ∀ i ∈ Finset.range k, ∀ p : ℕ, p.Prime → k < p → ¬ p ∣ (n + 1 + i) :=
    fun i hi p hp hkp hpd => hcon0 ⟨i, hi, p, hp, hkp, hpd⟩
  set N := n + k with hNdef
  have hpi : piCount k ≤ k := piCount_le_self k
  have hNpos : 0 < N := by omega
  -- there is no prime in the interval `(n, n+k]`
  have hnoprime : ∀ p : ℕ, p.Prime → n < p → p ≤ n + k → False := by
    intro p hp h1 h2
    refine hcon (p - n - 1) (Finset.mem_range.2 (by omega)) p hp (by omega) ?_
    have : n + 1 + (p - n - 1) = p := by omega
    rw [this]
  -- every prime factor of the binomial coefficient is at most `k`
  have hH : ∀ p : ℕ, p.Prime → p ∣ N.choose k → p ≤ k := by
    intro p hp hdvd
    by_contra hpk
    rw [not_le] at hpk
    have hdvd' : p ∣ N.descFactorial k := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      exact Dvd.dvd.mul_left hdvd _
    rw [Nat.descFactorial_eq_prod_range] at hdvd'
    obtain ⟨i, hi, hpi'⟩ := (Nat.Prime.prime hp).exists_mem_finset_dvd hdvd'
    rw [Finset.mem_range] at hi
    refine hcon (k - i - 1) (Finset.mem_range.2 (by omega)) p hp hpk ?_
    have : n + 1 + (k - i - 1) = N - i := by omega
    rw [this]
    exact hpi'
  rcases Nat.lt_or_ge k 26 with hk25 | hk25
  · rcases Nat.lt_or_ge n 200 with hn200 | hn200
    · obtain ⟨i, hi, p, hpmem, hkp, hpd⟩ :=
        small_cases k (Finset.mem_range.2 (by omega)) n (Finset.mem_range.2 hn200) hk h
      exact hcon i hi p (smallPrimes_prime p hpmem) hkp hpd
    · have h1 : N.choose k ≤ N ^ piCount k := choose_le_pow_piCount hNpos hH
      have h2 : N ^ k ≤ k ^ k * N.choose k := pow_le_pow_mul_choose (by omega)
      have h3 : k ^ k < 200 ^ (k - piCount k) :=
        small_pow_lt k (Finset.mem_range.2 (by omega)) hk
      have h4 : (200 : ℕ) ^ (k - piCount k) ≤ N ^ (k - piCount k) :=
        Nat.pow_le_pow_left (by omega) _
      have h5 : N ^ k < N ^ (k - piCount k) * N ^ piCount k := by
        calc N ^ k ≤ k ^ k * N.choose k := h2
          _ ≤ k ^ k * N ^ piCount k := by exact Nat.mul_le_mul_left _ h1
          _ < 200 ^ (k - piCount k) * N ^ piCount k := by
              exact mul_lt_mul_of_pos_right h3 (Nat.pow_pos hNpos)
          _ ≤ N ^ (k - piCount k) * N ^ piCount k := Nat.mul_le_mul_right _ h4
      rw [← pow_add] at h5
      rw [Nat.sub_add_cancel hpi] at h5
      exact absurd h5 (lt_irrefl _)
  · have hlow : 4 ^ k * N ^ k < k * ((2 * k) ^ k * N.choose k) :=
      four_pow_mul_pow_lt (by omega) (by omega)
    rcases Nat.lt_or_ge (N ^ 2) (k ^ 3) with hA | hA
    · rcases Nat.lt_or_ge k 20000 with hB | hB
      · have hn2 : n ^ 2 < k ^ 3 := by
          have : n ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left (by omega) 2
          omega
        have hk3 : k ^ 3 ≤ 19999 ^ 3 := Nat.pow_le_pow_left (by omega) 3
        have hnlt : n < 2828300 := by
          by_contra hcc
          rw [not_lt] at hcc
          have hsq : (2828300 : ℕ) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hcc 2
          norm_num at hsq hk3
          omega
        obtain ⟨p, hp, h1, h2⟩ := exists_prime_in_Ioc (by omega) hnlt hn2
        exact hnoprime p hp h1 h2
      · have h1 : N.choose k ≤ N ^ Nat.sqrt N * 4 ^ min k (N / 3) :=
          choose_le_pow_sqrt_mul_four_pow (by omega) (by omega) hH
        have h2 := caseB hB (by omega) hA
        have hcontr : (4 : ℕ) ^ k * N ^ k < 4 ^ k * N ^ k := by
          calc 4 ^ k * N ^ k < k * ((2 * k) ^ k * N.choose k) := hlow
            _ ≤ k * ((2 * k) ^ k * (N ^ Nat.sqrt N * 4 ^ min k (N / 3))) := by
                exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
            _ ≤ 4 ^ k * N ^ k := h2
        exact absurd hcontr (lt_irrefl _)
    · have h1 : N.choose k ≤ N ^ piCount k := choose_le_pow_piCount hNpos hH
      have h2 : k ^ (k + 1) < 2 ^ k * N ^ (k - piCount k) :=
        caseA (by omega) hA (three_mul_piCount_le k)
      have hcontr : (4 : ℕ) ^ k * N ^ k < 4 ^ k * N ^ k := by
        calc 4 ^ k * N ^ k < k * ((2 * k) ^ k * N.choose k) := hlow
          _ ≤ k * ((2 * k) ^ k * N ^ piCount k) := by
              exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
          _ = 2 ^ k * k ^ (k + 1) * N ^ piCount k := by ring
          _ < 2 ^ k * (2 ^ k * N ^ (k - piCount k)) * N ^ piCount k := by
              have h6 : 2 ^ k * k ^ (k + 1) < 2 ^ k * (2 ^ k * N ^ (k - piCount k)) :=
                mul_lt_mul_of_pos_left h2 (Nat.pow_pos (by norm_num))
              exact mul_lt_mul_of_pos_right h6 (Nat.pow_pos hNpos)
          _ = 4 ^ k * (N ^ (k - piCount k) * N ^ piCount k) := by
              rw [show (4:ℕ) = 2 * 2 by norm_num, mul_pow]; ring
          _ = 4 ^ k * N ^ k := by
              rw [← pow_add, Nat.sub_add_cancel hpi]
      exact absurd hcontr (lt_irrefl _)

end Brockian.SylvesterSchur


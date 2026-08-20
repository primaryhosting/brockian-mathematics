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

theorem choose_le_pow_piCount {N k : ℕ} (hN : 0 < N)
    (H : ∀ p : ℕ, p.Prime → p ∣ N.choose k → p ≤ k) :
    N.choose k ≤ N ^ piCount k := by
  by_cases h : N.choose k = 0
  · simp [h]
  · have hpos : 0 < N.choose k := Nat.pos_of_ne_zero h
    have heq : N.choose k = (Nat.factorization (N.choose k)).prod fun p e => p ^ e := by
             rw [Nat.prod_factorization_pow_eq_self hpos.ne']
    calc N.choose k = (Nat.factorization (N.choose k)).prod fun p e => p ^ e := heq
       _ ≤ ∏ _p ∈ (N.choose k).primeFactors, N := by
             apply Finset.prod_le_prod'
             intro p hp
             have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
             have hp_dvd : p ∣ N.choose k := Nat.dvd_of_mem_primeFactors hp
             have hp_le : p ≤ k := H p hp_prime hp_dvd
             -- Need to show p^e ≤ N where e = v_p(N.choose k)
             -- This follows from e ≤ log_p(N)
             have he_bound : (N.choose k).factorization p ≤ Nat.log p N :=
               Nat.factorization_choose_le_log
             calc p ^ (N.choose k).factorization p ≤ p ^ Nat.log p N :=
                     Nat.pow_le_pow_right hp_prime.one_lt.le he_bound
               _ ≤ N := Nat.pow_log_le_self p (by omega)
       _ = N ^ (N.choose k).primeFactors.card := by simp
       _ ≤ N ^ piCount k := by
             apply Nat.pow_le_pow_right (Nat.one_le_iff_ne_zero.mpr (ne_of_gt hN)).ge
             apply Finset.card_le_card
             intro p hp
             simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
             exact ⟨H p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp),
               Nat.prime_of_mem_primeFactors hp⟩

/-- A refined upper bound: primes `p` with `N < 3 * p` do not divide `N.choose k`. -/

import Mathlib
namespace Brockian.OddPerfectThreePrimes

open Finset

/-- For a prime `p`, `(p-1) * σ₁(p^a) = p^(a+1) - 1 < p * p^a`. -/

private lemma sigma_prod_bound {n : ℕ} (hn : n ≠ 0) (hne : n.primeFactors.Nonempty) :
    (∏ p ∈ n.primeFactors, (p - 1)) * (∑ d ∈ n.divisors, d)
      < (∏ p ∈ n.primeFactors, p) * n := by
  -- Prime powers at different primes are coprime
  have hcoprime : ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, p ≠ q →
      Nat.Coprime (p ^ (n.factorization p)) (q ^ (n.factorization q)) := by
    intro p hp q hq hneq
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hqq : Nat.Prime q := Nat.prime_of_mem_primeFactors hq
    exact Nat.coprime_pow_primes _ _ hpp hqq hneq
  -- All prime powers are positive
  have hpos : ∀ p ∈ n.primeFactors, 0 < p ^ (n.factorization p) := by
    intro p hp
    exact pow_pos (Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp)) _
  have hsum_divisors : ∑ d ∈ n.divisors, d
      = ∏ p ∈ n.primeFactors, ∑ d ∈ (p ^ (n.factorization p)).divisors, d := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    exact sum_divisors_prod _ _ hcoprime (fun p hp => (hpos p hp).ne')
  -- Now use hsum_divisors to complete the proof
  rw [hsum_divisors]
  -- Use sigma_primePow_bound for each factor
  have h_bound : ∏ p ∈ n.primeFactors, ((p - 1) * ∑ d ∈ (p ^ (n.factorization p)).divisors, d) <
      ∏ p ∈ n.primeFactors, p * p ^ (n.factorization p) := by
    apply Finset.prod_lt_prod_of_nonempty
    · intro p hp
      have hp_pos : 0 < p := Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp)
      have hsum_pos : 0 < ∑ d ∈ (p ^ (n.factorization p)).divisors, d := by
        apply Finset.sum_pos
        · intro d hd
          exact Nat.pos_of_mem_divisors hd
        · exact ⟨1, Nat.one_mem_divisors.mpr (pow_ne_zero _ hp_pos.ne')⟩
      exact Nat.mul_pos (Nat.sub_pos_of_lt (Nat.Prime.one_lt (Nat.prime_of_mem_primeFactors hp))) hsum_pos
    · intro p hp
      exact sigma_primePow_bound (Nat.prime_of_mem_primeFactors hp) (n.factorization p)
    · exact hne
  rw [Finset.prod_mul_distrib] at h_bound
  -- Now show that (∏ p) * (∏ p^a) = (∏ p) * n
  have hprod_eq : ∏ p ∈ n.primeFactors, p * p ^ (n.factorization p) =
      (∏ p ∈ n.primeFactors, p) * (∏ p ∈ n.primeFactors, p ^ (n.factorization p)) :=
    Finset.prod_mul_distrib
  have hprod_pow : ∏ p ∈ n.primeFactors, p ^ (n.factorization p) = n :=
    Nat.prod_factorization_pow_eq_self hn
  rw [hprod_eq, hprod_pow] at h_bound
  exact h_bound

/-- If a finite set of integers `≥ 3` has at most two elements, then `∏ p ≤ 2 * ∏ (p-1)`. -/

import Mathlib

namespace Brockian.OddPerfectThreePrimes

open Finset

/-- A geometric-sum identity: `(1 + p + ⋯ + p ^ a) * (p - 1) + 1 = p ^ (a + 1)`. -/

lemma odd_deficient_of_primeFactors_eq_pair {n p q : ℕ} (ho : Odd n) (hpq : p ≠ q)
    (hS : n.primeFactors = {p, q}) : Nat.Deficient n := by
  have hn : n ≠ 0 := by rintro rfl; simp at ho
  have hp_mem : p ∈ n.primeFactors := by rw [hS]; simp
  have hq_mem : q ∈ n.primeFactors := by rw [hS]; simp
  have hp3 : 3 ≤ p := three_le_of_mem_primeFactors ho hp_mem
  have hq3 : 3 ≤ q := three_le_of_mem_primeFactors ho hq_mem
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
  -- Since `p ≠ q` and both are odd primes, one of them is at least 5
  have step (r : ℕ) (hr : r.Prime) (hr3 : 3 ≤ r) : r = 3 ∨ 5 ≤ r := by
    have h4 : r ≠ 4 := by rintro rfl; norm_num at hr
    omega
  have bound : (3 ≤ p ∧ 5 ≤ q) ∨ (5 ≤ p ∧ 3 ≤ q) := by
    rcases step p hp_prime hp3 with rfl | hp5
    · rcases step q hq_prime hq3 with rfl | hq5
      · exact absurd rfl hpq
      · exact Or.inl ⟨hp3, hq5⟩
    · exact Or.inr ⟨hp5, hq3⟩
  -- Rewrite n as p^a * q^b
  have hfactor : n = p ^ (n.factorization p) * q ^ (n.factorization q) :=
    eq_pow_mul_pow_of_primeFactors_eq_pair hn hpq hS
  -- Apply the bound
  rw [hfactor]
  rcases bound with ⟨hp3', hq5⟩ | ⟨hp5, hq3'⟩
  · exact deficient_of_sum_divisors_lt (sum_divisors_lt_two_mul_of_two_primes hp_prime hq_prime hpq hp3' hq5)
  · rw [mul_comm]
    exact deficient_of_sum_divisors_lt (sum_divisors_lt_two_mul_of_two_primes hq_prime hp_prime hpq.symm hq3' hp5)

/-- An odd natural number with at most two distinct prime factors is deficient. -/

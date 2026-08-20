/-
  Aristotle target — Euler's theorem on odd perfect numbers (a genuine hard partial
  result toward the ancient odd-perfect-number problem; existence remains OPEN).

  If n is odd and perfect, then n has Euler's form n = p^k * m^2 with p prime,
  p ≡ 1 (mod 4), k ≡ 1 (mod 4), and p ∤ m.
-/
import Mathlib

namespace Brockian.OddPerfectEuler

open ArithmeticFunction


private lemma reconstruct_euler_factorization {n p k : ℕ}
    (hn : n ≠ 0) (hp : p.Prime) (hk : n.factorization p = k)
    (hother : ∀ q ∈ n.primeFactors, q ≠ p → Even (n.factorization q)) :
    ∃ m : ℕ, ¬ p ∣ m ∧ n = p ^ k * m ^ 2 := by
  -- First, express n using its prime factorization
  have hprod : n = ∏ q ∈ n.primeFactors, q ^ n.factorization q :=
    Eq.symm (Nat.factorization_prod_pow_eq_self hn)
  by_cases hp_mem : p ∈ n.primeFactors
  · -- p is a prime factor
    -- Separate p from the product
    have hsplits : n = p ^ k * ∏ q ∈ n.primeFactors \ {p}, q ^ n.factorization q := by
      conv_lhs => rw [hprod]
      rw [← Finset.prod_sdiff (Finset.singleton_subset_iff.mpr hp_mem)]
      simp [Finset.prod_singleton]
      rw [hk]
      ring
    -- All primes in the set n.primeFactors \ {p} have even exponents
    have hall_even : ∀ q ∈ n.primeFactors \ {p}, Even (n.factorization q) := by
      intro q hq
      exact hother q (Finset.mem_sdiff.mp hq |>.1) (fun hqp => Finset.mem_singleton.not.mp (Finset.mem_sdiff.mp hq |>.2) hqp)
    -- Define m as the product over n.primeFactors \ {p}
    let m := ∏ q ∈ n.primeFactors \ {p}, q ^ (n.factorization q / 2)
    use m
    -- Show p ∤ m
    have hp_ne_m : ¬ p ∣ m := by
      rw [Nat.Prime.dvd_iff_not_coprime hp]
      push_neg
      apply Nat.Coprime.prod_right
      intro q hq
      refine hp.coprime_iff_not_dvd.mpr ?_
      intro hqdiv
      have hpq : p = q := by
        have : p ∣ q := hp.dvd_of_dvd_pow hqdiv
        exact (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq |>.1))).mp this
      exact Finset.mem_singleton.not.mp (Finset.mem_sdiff.mp hq |>.2) hpq.symm
    refine ⟨hp_ne_m, ?_⟩
    rw [hsplits]
    congr 1
    show ∏ q ∈ n.primeFactors \ {p}, q ^ n.factorization q = m ^ 2
    symm
    rw [pow_two]
    trans ∏ q ∈ n.primeFactors \ {p}, (q ^ (n.factorization q / 2)) * (q ^ (n.factorization q / 2))
    · rw [← Finset.prod_mul_distrib]
    · refine Finset.prod_congr rfl ?_
      intro q hq
      have heven := hall_even q hq
      rw [← pow_add]
      congr 1
      linarith [Nat.div_mul_cancel heven.two_dvd]
  · -- p is not a prime factor, so k = 0
    have hk0 : k = 0 := by
      have : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd (fun h => hp_mem (Nat.mem_primeFactors.mpr ⟨hp, h, hn⟩))
      rw [← hk, this]
    -- All prime factors of n have even exponents, so n is a perfect square
    have hall_even : ∀ q ∈ n.primeFactors, Even (n.factorization q) := by
      intro q hq
      exact hother q hq (fun hqp => hp_mem (hqp.symm ▸ hq))
    -- Define m as the product of q^(n.factorization q / 2)
    let m := ∏ q ∈ n.primeFactors, q ^ (n.factorization q / 2)
    use m
    have hp_ne_m : ¬ p ∣ m := by
      rw [Nat.Prime.dvd_iff_not_coprime hp]
      push_neg
      apply Nat.Coprime.prod_right
      intro q hq
      refine hp.coprime_iff_not_dvd.mpr ?_
      intro hqdiv
      have : p ∣ q := hp.dvd_of_dvd_pow hqdiv
      have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hq)).mp this |>.symm
      exact hp_mem (hqp ▸ hq)
    refine ⟨hp_ne_m, ?_⟩
    simp [hk0]
    rw [hprod]
    symm
    show (∏ q ∈ n.primeFactors, q ^ (n.factorization q / 2)) ^ 2 = ∏ q ∈ n.primeFactors, q ^ n.factorization q
    rw [pow_two]
    trans ∏ q ∈ n.primeFactors, (q ^ (n.factorization q / 2)) * (q ^ (n.factorization q / 2))
    · rw [← Finset.prod_mul_distrib]
    · refine Finset.prod_congr rfl ?_
      intro q hq
      have heven := hall_even q hq
      rw [← pow_add]
      congr 1
      linarith [Nat.div_mul_cancel heven.two_dvd]

/-- **Euler's form for odd perfect numbers.** -/

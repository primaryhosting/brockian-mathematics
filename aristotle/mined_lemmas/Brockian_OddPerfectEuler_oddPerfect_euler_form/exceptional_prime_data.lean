/-
  Aristotle target — Euler's theorem on odd perfect numbers (a genuine hard partial
  result toward the ancient odd-perfect-number problem; existence remains OPEN).

  If n is odd and perfect, then n has Euler's form n = p^k * m^2 with p prime,
  p ≡ 1 (mod 4), k ≡ 1 (mod 4), and p ∤ m.
-/
import Mathlib

namespace Brockian.OddPerfectEuler

open ArithmeticFunction


private lemma exceptional_prime_data {n : ℕ} (hn : n ≠ 0) (hodd : Odd n)
    (hsigma : (sigma 1) n = 2 * n) :
    ∃ p ∈ n.primeFactors,
      (∑ i ∈ Finset.range (n.factorization p + 1), p ^ i) % 4 = 2 ∧
      ∀ q ∈ n.primeFactors, q ≠ p → Even (n.factorization q) := by
  let f : ℕ → ℕ := fun p =>
    ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i
  have hprod : (∏ p ∈ n.primeFactors, f p) % 4 = 2 := by
    have heq : (∏ p ∈ n.primeFactors, f p) = 2 * n := by
      rw [← hsigma, sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
      simp [f]
    rw [heq]
    obtain ⟨a, rfl⟩ := hodd
    omega
  obtain ⟨p, hp, hp2⟩ :=
    exists_factor_mod_four_eq_two n.primeFactors f hprod
  refine ⟨p, hp, hp2, ?_⟩
  intro q hq hqp
  have hfp_even : f p % 2 = 0 := by omega
  have hfq_odd : f q % 2 = 1 :=
    other_factor_odd n.primeFactors f hprod hp hq hfp_even hqp
  have hqodd : q % 2 = 1 := by
    rw [← Nat.odd_iff]
    exact hodd.of_dvd_nat (Nat.mem_primeFactors.mp hq).2.1
  have hparity := geom_sum_parity (e := n.factorization q) hqodd
  rw [Nat.even_iff]
  dsimp [f] at hfq_odd
  omega


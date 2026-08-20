import Mathlib
namespace C5.NT7

open ArithmeticFunction Finset

open scoped sigma

/-- `σ 1 (2 ^ k) = 2 ^ (k + 1) - 1`, i.e. the sum of divisors of a power of two is the
corresponding Mersenne number. -/

theorem even_perfect_form (n : ℕ) (hn : Nat.Perfect n) (he : Even n) :
    ∃ p : ℕ, (2^p - 1).Prime ∧ n = 2^(p-1)*(2^p - 1) := by
  obtain ⟨k, hpr, hk⟩ := eq_two_pow_mul_prime_mersenne_of_even_perfect he hn
  exact ⟨k + 1, hpr, by simpa [mersenne] using hk⟩


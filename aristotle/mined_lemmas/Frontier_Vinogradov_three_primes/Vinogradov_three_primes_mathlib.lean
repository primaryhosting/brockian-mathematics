import Mathlib
import RequestProject.Vinogradov

/-!
# Vinogradov three primes: Mathlib-phrased companion

`RequestProject/Vinogradov.lean` is import-free (its required header comment must be the
very first thing in the file, and Lean forbids `import` after any other command), so it
uses a self-contained trial-division primality predicate `Frontier.IsPrime` and encodes
oddness as `n % 2 = 1`.  Here we check that these agree with Mathlib's `Nat.Prime` and
`Odd`, and restate the results in Mathlib's vocabulary.
-/

namespace Frontier

/-- The trial-division predicate used in the import-free file agrees with `Nat.Prime`. -/

theorem Vinogradov_three_primes_mathlib
    (hG : ∀ n : ℕ, 4 ≤ n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n →
      ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = n := by
  obtain ⟨N, hN⟩ := Vinogradov_three_primes fun n hn hodd => by
    obtain ⟨p, q, hp, hq, hpq⟩ := hG n hn (Nat.even_iff.mpr hodd)
    exact ⟨p, q, (isPrime_iff_nat_prime p).mpr hp, (isPrime_iff_nat_prime q).mpr hq, hpq⟩
  exact ⟨N, fun n hn hodd => (isSumOfThreePrimes_iff n).mp (hN n hn (Nat.odd_iff.mp hodd))⟩

/-- Mathlib-phrased form of the unconditional base case. -/

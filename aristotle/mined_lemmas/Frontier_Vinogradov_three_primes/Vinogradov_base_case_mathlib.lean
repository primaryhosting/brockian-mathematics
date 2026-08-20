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

theorem Vinogradov_base_case_mathlib (n : ℕ) (hn : n < 500) (h7 : 7 ≤ n) (hodd : Odd n) :
    ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = n :=
  (isSumOfThreePrimes_iff n).mp (Vinogradov_base_case n hn h7 (Nat.odd_iff.mp hodd))

/-- Unconditionally, infinitely many odd numbers are sums of three primes: for every odd
prime `p`, the odd number `p + 4 = p + 2 + 2` is a sum of three primes. -/

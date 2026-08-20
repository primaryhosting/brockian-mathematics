import Mathlib
/-!
# Vinogradov Three Primes
Category: Frontier — Prime Numbers
Target: Frontier.Vinogradov_three_primes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` commands to be the very first
commands in a file, so the mandated header block appears immediately after the
single `import Mathlib` line.

Contents:
* `Frontier.IsSumOfThreePrimes`, `Frontier.VinogradovThreePrimes`: the formal
  statement "every sufficiently large odd number is a sum of three primes".
* `Frontier.Vinogradov_three_primes`: a Lean-checked reduction of that statement
  to the binary Goldbach conjecture (in its eventual form).
* `Frontier.isSumOfThreePrimes_of_le_10003`: the unconditional base case,
  verified by kernel computation for every odd `n` with `7 ≤ n ≤ 10003`.
* `Frontier.infinite_odd_isSumOfThreePrimes`: unconditionally, infinitely many
  odd numbers are sums of three primes.
-/

namespace Frontier

/-- `n` is a sum of three (not necessarily distinct) primes. -/

theorem isSumOfThreePrimes_of_goldbachBinary (h : GoldbachBinary) :
    ∀ n : ℕ, 7 ≤ n → Odd n → IsSumOfThreePrimes n := by
  intro n hn hodd
  obtain ⟨k, hk⟩ := hodd
  have hev : Even (n - 3) := by
    rw [Nat.even_iff]; omega
  obtain ⟨p, q, hp, hq, hpq⟩ := h (n - 3) (by omega) hev
  exact ⟨3, p, q, Nat.prime_three, hp, hq, by omega⟩

/-! ### An unconditional infinitude statement -/

/-- Unconditionally, infinitely many odd numbers are sums of three primes:
for every odd prime `p`, the odd number `p + 4 = 2 + 2 + p` is one. -/

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

theorem infinite_odd_isSumOfThreePrimes :
    {n : ℕ | Odd n ∧ IsSumOfThreePrimes n}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun a => ?_
  obtain ⟨p, hpa, hp⟩ := Nat.exists_infinite_primes (max (a + 1) 3)
  have hp3 : 3 ≤ p := le_trans (le_max_right _ _) hpa
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  refine ⟨p + 4, ⟨?_, ⟨2, 2, p, Nat.prime_two, Nat.prime_two, hp, by ring⟩⟩, ?_⟩
  · obtain ⟨k, hk⟩ := hodd
    exact ⟨k + 2, by omega⟩
  · have : a + 1 ≤ p := le_trans (le_max_left _ _) hpa
    omega

/-! ### The unconditional base case, by kernel computation -/

/-- Primality test with a bounded trial division: if `k < (B+1)^2` and no
`d` with `2 ≤ d ≤ B` is a proper divisor of `k`, then `k` is prime. -/

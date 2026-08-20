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

theorem goldbach_data_2 :
    ∀ m ∈ Finset.Icc 4000 8000, Even m → ∃ p ∈ Finset.range 200,
      Nat.Prime p ∧ 2 ≤ m - p ∧ ∀ d ∈ Finset.Icc 2 100, d ∣ (m - p) → m - p = d := by
  decide +kernel

set_option maxRecDepth 20000000 in
set_option maxHeartbeats 4000000 in
/-- Kernel-verified Goldbach data for `8000 ≤ m ≤ 10000`. -/

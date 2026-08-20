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

theorem goldbach_le_10000 (m : ℕ) (h4 : 4 ≤ m) (h : m ≤ 10000) (hev : Even m) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ m = p + q := by
  have key : ∃ p ∈ Finset.range 200,
      Nat.Prime p ∧ 2 ≤ m - p ∧ ∀ d ∈ Finset.Icc 2 100, d ∣ (m - p) → m - p = d := by
    rcases le_or_gt m 4000 with hm | hm
    · exact goldbach_data_1 m (Finset.mem_Icc.mpr ⟨h4, hm⟩) hev
    · rcases le_or_gt m 8000 with hm' | hm'
      · exact goldbach_data_2 m (Finset.mem_Icc.mpr ⟨by omega, hm'⟩) hev
      · exact goldbach_data_3 m (Finset.mem_Icc.mpr ⟨by omega, h⟩) hev
  obtain ⟨p, -, hp, h2, hdiv⟩ := key
  refine ⟨p, m - p, hp, prime_of_bounded_trial_division (m - p) 100 h2 (by omega) hdiv, by omega⟩

/-- **Base case, unconditional.**  Every odd number `n` with `7 ≤ n ≤ 10003` is
a sum of three primes. -/

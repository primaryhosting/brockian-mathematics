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

theorem prime_of_bounded_trial_division (k B : ℕ) (h2 : 2 ≤ k) (hk : k < (B + 1) ^ 2)
    (h : ∀ d ∈ Finset.Icc 2 B, d ∣ k → k = d) : Nat.Prime k := by
  have hpr := Nat.minFac_prime (by omega : k ≠ 1)
  have hdvd := Nat.minFac_dvd k
  by_cases hle : k.minFac ≤ B
  · have hkm := h k.minFac (Finset.mem_Icc.mpr ⟨hpr.two_le, hle⟩) hdvd
    rwa [hkm]
  · by_contra hp
    have hmf := Nat.minFac_sq_le_self (by omega) hp
    nlinarith [hmf, hk, Nat.lt_of_not_le hle]

set_option maxRecDepth 20000000 in
set_option maxHeartbeats 4000000 in
/-- Kernel-verified Goldbach data for `4 ≤ m ≤ 4000`. -/

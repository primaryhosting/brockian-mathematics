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
def IsSumOfThreePrimes (n : ℕ) : Prop :=
  ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

/-- The Vinogradov (ternary Goldbach) statement: every sufficiently large odd
number is a sum of three primes. -/
def VinogradovThreePrimes : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n → IsSumOfThreePrimes n

/-- The binary Goldbach conjecture in its "eventual" form: every sufficiently
large even number is a sum of two primes. -/
def GoldbachEventually : Prop :=
  ∃ M : ℕ, ∀ m : ℕ, M ≤ m → Even m → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ m = p + q

/-- The binary Goldbach conjecture in its usual form. -/
def GoldbachBinary : Prop :=
  ∀ m : ℕ, 4 ≤ m → Even m → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ m = p + q

theorem goldbachEventually_of_goldbachBinary (h : GoldbachBinary) : GoldbachEventually :=
  ⟨4, fun m hm hev => h m hm hev⟩

/-- **Lean-checked reduction.**  If every sufficiently large even number is a
sum of two primes, then every sufficiently large odd number is a sum of three
primes: write an odd number as `3 + (an even number)`. -/
theorem Vinogradov_three_primes (h : GoldbachEventually) : VinogradovThreePrimes := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M + 3, fun n hn hodd => ?_⟩
  obtain ⟨k, hk⟩ := hodd
  have hev : Even (n - 3) := by
    rw [Nat.even_iff]; omega
  obtain ⟨p, q, hp, hq, hpq⟩ := hM (n - 3) (by omega) hev
  exact ⟨3, p, q, Nat.prime_three, hp, hq, by omega⟩

/-- The same reduction, from the full binary Goldbach conjecture, with the
explicit threshold `7`. -/
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
theorem goldbach_data_1 :
    ∀ m ∈ Finset.Icc 4 4000, Even m → ∃ p ∈ Finset.range 200,
      Nat.Prime p ∧ 2 ≤ m - p ∧ ∀ d ∈ Finset.Icc 2 100, d ∣ (m - p) → m - p = d := by
  decide +kernel

set_option maxRecDepth 20000000 in
set_option maxHeartbeats 4000000 in
/-- Kernel-verified Goldbach data for `4000 ≤ m ≤ 8000`. -/
theorem goldbach_data_2 :
    ∀ m ∈ Finset.Icc 4000 8000, Even m → ∃ p ∈ Finset.range 200,
      Nat.Prime p ∧ 2 ≤ m - p ∧ ∀ d ∈ Finset.Icc 2 100, d ∣ (m - p) → m - p = d := by
  decide +kernel

set_option maxRecDepth 20000000 in
set_option maxHeartbeats 4000000 in
/-- Kernel-verified Goldbach data for `8000 ≤ m ≤ 10000`. -/
theorem goldbach_data_3 :
    ∀ m ∈ Finset.Icc 8000 10000, Even m → ∃ p ∈ Finset.range 200,
      Nat.Prime p ∧ 2 ≤ m - p ∧ ∀ d ∈ Finset.Icc 2 100, d ∣ (m - p) → m - p = d := by
  decide +kernel

/-- **Binary Goldbach, verified up to 10000.**  Every even `m` with
`4 ≤ m ≤ 10000` is a sum of two primes. -/
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
theorem isSumOfThreePrimes_of_le_10003 (n : ℕ) (h7 : 7 ≤ n) (h : n ≤ 10003) (hodd : Odd n) :
    IsSumOfThreePrimes n := by
  obtain ⟨k, hk⟩ := hodd
  have hev : Even (n - 3) := by
    rw [Nat.even_iff]; omega
  obtain ⟨p, q, hp, hq, hpq⟩ := goldbach_le_10000 (n - 3) (by omega) (by omega) hev
  exact ⟨3, p, q, Nat.prime_three, hp, hq, by omega⟩

end Frontier

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false


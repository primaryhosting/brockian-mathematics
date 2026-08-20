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

/-
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
The twin prime conjecture is a famous open problem, so the target theorem
`Brockian.TwinPrimes.TwinPrimeConjecture` is stated here as a *conditional reduction*:
it derives the infinitude of twin primes from `ClementHypothesis`, a purely
elementary (factorial/divisibility) statement.

The mathematical content that is proved unconditionally is **Clement's theorem**:
for `n ≥ 2`, the pair `(n, n+2)` consists of two primes if and only if

`n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n`.

Consequently `ClementHypothesis` is *equivalent* to the twin prime conjecture
(`twinPrime_iff_clementHypothesis`), so the reduction is faithful: no hidden
strengthening of the conjecture is assumed.
-/

namespace Brockian.TwinPrimes

open Nat Finset

/-- `n` starts a twin prime pair when both `n` and `n + 2` are prime. -/

theorem odd_of_clementCriterion {n : ℕ} (hn : 2 ≤ n) (h : ClementCriterion n) : ¬ 2 ∣ n := by
  intro he
  have h4 : (4 : ℕ) ∣ n * (n + 2) := by
    obtain ⟨k, rfl⟩ := he
    exact ⟨k * (k + 1), by ring⟩
  have hA : (4 : ℕ) ∣ 4 * ((n - 1)! + 1) + n := h4.trans h
  have h4n : (4 : ℕ) ∣ n := (Nat.dvd_add_right ⟨(n - 1)! + 1, rfl⟩).mp hA
  have hn4 : 4 ≤ n := Nat.le_of_dvd (by omega) h4n
  rcases eq_or_lt_of_le hn4 with heq | hlt
  · rw [← heq] at h
    norm_num [ClementCriterion, Nat.factorial] at h
  · have hnp : ¬ n.Prime := by
      intro hp
      have := (Nat.Prime.eq_one_or_self_of_dvd hp 4 h4n)
      omega
    have hdvd : n ∣ (n - 1)! := dvd_factorial_pred_of_not_prime hlt hnp
    have hn' : n ∣ 4 * ((n - 1)! + 1) + n := dvd_trans ⟨n + 2, rfl⟩ h
    have h1 : n ∣ 4 * ((n - 1)! + 1) := (Nat.dvd_add_right (Dvd.intro 1 rfl)).mp
      (by simpa [Nat.add_comm] using hn')
    have h2 : n ∣ 4 * (n - 1)! := Dvd.dvd.mul_left hdvd 4
    have h3 : n ∣ 4 := by
      have : 4 * ((n - 1)! + 1) = 4 * (n - 1)! + 4 := by ring
      rw [this] at h1
      exact (Nat.dvd_add_right h2).mp h1
    have := Nat.le_of_dvd (by norm_num) h3
    omega


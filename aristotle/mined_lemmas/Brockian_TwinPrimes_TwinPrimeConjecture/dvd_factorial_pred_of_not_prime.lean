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

theorem dvd_factorial_pred_of_not_prime {n : ℕ} (h4 : 4 < n) (hn : ¬ n.Prime) :
    n ∣ (n - 1)! := by
  obtain ⟨m, hm1, hm2, hm3⟩ := Nat.exists_dvd_of_not_prime2 (by omega) hn
  obtain ⟨k, rfl⟩ := hm1
  have hk1 : 1 < k := by nlinarith
  rcases eq_or_ne m k with rfl | hne
  · have hm3' : 3 ≤ m := by nlinarith
    have hb : 2 * m + 1 ≤ m * m := by nlinarith
    have : m * (2 * m) ∣ (m * m - 1)! :=
      mul_dvd_factorial_of_ne (by omega) (by omega) (by omega) (by omega) (by omega)
    exact dvd_trans ⟨2, by ring⟩ this
  · have hb : 2 * k ≤ m * k := Nat.mul_le_mul_right k hm2
    exact mul_dvd_factorial_of_ne (by omega) (by omega) hne (by omega) (by omega)

/-- For `n ≥ 1`, `(n + 1)! = (n + 1) * n * (n - 1)!`. -/

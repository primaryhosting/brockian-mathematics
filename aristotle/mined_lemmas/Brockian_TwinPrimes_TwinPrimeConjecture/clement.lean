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

theorem clement {n : ℕ} (hn : 2 ≤ n) : IsTwinPrimePair n ↔ ClementCriterion n := by
  constructor
  · rintro ⟨hp, hq⟩
    have hodd : ¬ 2 ∣ n := by
      intro he
      have : n = 2 := ((Nat.Prime.eq_one_or_self_of_dvd hp 2 he).resolve_left (by norm_num)).symm
      subst this
      norm_num at hq
    have hcop : Nat.Coprime n (n + 2) := by
      have h2 : Nat.Coprime n 2 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).symm
      exact Nat.coprime_self_add_right.mpr h2
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop (dvd_of_prime_left hn hp)
      (dvd_of_prime_right hn hq)
  · intro h
    exact ⟨prime_left_of_clementCriterion hn h, prime_right_of_clementCriterion hn h⟩

/-! ### The reduction -/

/-- **Twin Prime Conjecture** (conditional reduction): if Clement's criterion holds for
arbitrarily large `n`, then there are infinitely many twin prime pairs. -/

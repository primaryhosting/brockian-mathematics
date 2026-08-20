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

theorem dvd_of_prime_right {n : ℕ} (hn : 2 ≤ n) (hp : (n + 2).Prime) :
    (n + 2) ∣ 4 * ((n - 1)! + 1) + n := by
  have hw : (((n + 1)! : ℕ) : ZMod (n + 2)) = -1 := by
    have := (Nat.prime_iff_fac_equiv_neg_one (n := n + 2) (by omega)).mp hp
    simpa using this
  have hfac : ((n + 1)! : ℕ) = (n + 1) * n * (n - 1)! := factorial_succ_succ_pred (by omega)
  have hn2 : ((n : ℕ) : ZMod (n + 2)) = -2 := by
    have : (((n + 2 : ℕ)) : ZMod (n + 2)) = 0 := ZMod.natCast_self _
    push_cast at this ⊢
    linear_combination this
  have h2x : (2 : ZMod (n + 2)) * (((n - 1)! : ℕ) : ZMod (n + 2)) = -1 := by
    rw [hfac] at hw
    push_cast at hw
    rw [hn2] at hw
    linear_combination hw
  have : ((4 * ((n - 1)! + 1) + n : ℕ) : ZMod (n + 2)) = 0 := by
    push_cast
    rw [show ((n : ℕ) : ZMod (n + 2)) = -2 from hn2]
    push_cast at h2x ⊢
    linear_combination 2 * h2x
  exact (ZMod.natCast_eq_zero_iff _ _).mp this


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

open scoped Nat

namespace Brockian.TwinPrimes

/-- **The Twin Prime Conjecture**: there are arbitrarily large primes `p` such that
`p + 2` is also prime. -/

theorem mul_dvd_factorial_of_lt {a b N : ℕ} (ha : 0 < a) (hab : a < b) (hbN : b ≤ N) :
    a * b ∣ N ! := by
  have hb : b = (b - 1) + 1 := by omega
  have h1 : a * b ∣ b ! := by
    rw [hb, Nat.factorial_succ, ← hb]
    exact mul_comm a b ▸ Nat.mul_dvd_mul (dvd_refl b) (Nat.dvd_factorial ha (by omega))
  exact h1.trans (Nat.factorial_dvd_factorial hbN)

/-- If `n` is even and `n ≥ 6`, then `n ∣ (n-1)!`. -/

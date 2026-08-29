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

import Mathlib

/-!
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.AndricaConjecture

/-- **Oppermann's conjecture** (open): for every `n ≥ 2` there is a prime strictly between
`n²` and `n² + n`, and a prime strictly between `n² + n` and `(n+1)²`. -/

theorem andrica_of_prime_gap {n : ℕ}
    (h : Nat.nth Nat.Prime (n + 1) <
      Nat.nth Nat.Prime n + 2 * Nat.sqrt (Nat.nth Nat.Prime n) + 1) :
    Real.sqrt (Nat.nth Nat.Prime (n + 1)) - Real.sqrt (Nat.nth Nat.Prime n) < 1 :=
  sqrt_sub_sqrt_lt_one (by simpa [pow_two] using Nat.sqrt_le' (Nat.nth Nat.Prime n)) h

/-- Unconditional partial result: Andrica's inequality holds for the first few primes. -/

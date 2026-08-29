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

open Real

/-- `prime n` is the `n`-th prime number (`prime 0 = 2`, `prime 1 = 3`, ...). -/

theorem andrica_of_exists_prime {n q : ℕ} (hq : Nat.Prime q) (hlt : prime n < q)
    (hbound : (q : ℝ) < (prime n : ℝ) + 2 * Real.sqrt (prime n) + 1) :
    Real.sqrt (prime (n + 1)) - Real.sqrt (prime n) < 1 := by
  have hle : (prime (n + 1) : ℝ) ≤ (q : ℝ) := Nat.cast_le.2 (prime_succ_le hq hlt)
  exact (sqrt_sub_sqrt_lt_one_iff (by positivity)).2 (by linarith)

/-! ## Oppermann's conjecture implies the prime-gap bound -/

/-- Under Oppermann's conjecture, consecutive primes satisfy `pₙ₊₁ < pₙ + 2√pₙ + 1`. -/

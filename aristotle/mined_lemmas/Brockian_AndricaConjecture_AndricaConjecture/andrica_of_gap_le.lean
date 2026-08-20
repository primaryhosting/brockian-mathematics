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
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 does not allow a
-- module docstring to precede the `import` line.)

import Mathlib

namespace Brockian.AndricaConjecture

open scoped Nat

/-! ## The sequence of primes -/

/-- The set of primes is infinite. -/

theorem andrica_of_gap_le (n : ℕ)
    (h : nthPrime (n + 1) ≤ nthPrime n + 2 * Nat.sqrt (nthPrime n)) :
    Real.sqrt (nthPrime (n + 1)) - Real.sqrt (nthPrime n) < 1 :=
  andrica_of_gap_le_two_mul n (Nat.sqrt (nthPrime n))
    (by simpa [pow_two] using Nat.sqrt_le' (nthPrime n)) h

/-! ## The first few instances, unconditionally -/

/-- If `q` is prime, `p_n < q`, and no number strictly between `p_n` and `q` is prime,
then `q` is the next prime after `p_n`. -/

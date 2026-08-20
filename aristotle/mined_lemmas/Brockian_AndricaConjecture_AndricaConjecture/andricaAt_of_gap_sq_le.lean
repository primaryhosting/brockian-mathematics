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

import Mathlib

/-!
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000

namespace Brockian.AndricaConjecture

/-- `nthPrime n` is the `n`-th prime number (`nthPrime 0 = 2`, `nthPrime 1 = 3`, ...). -/

theorem andricaAt_of_gap_sq_le (n : ℕ)
    (h : (nthPrime (n + 1) - nthPrime n) ^ 2 ≤ 4 * nthPrime n) : AndricaAt n := by
  refine (andricaAt_iff n).mpr (lt_of_lt_of_le ?_ h)
  have hlt : nthPrime n < nthPrime (n + 1) := nthPrime_lt_nthPrime_succ n
  have h1 : nthPrime (n + 1) - nthPrime n - 1 < nthPrime (n + 1) - nthPrime n := by omega
  exact Nat.pow_lt_pow_left h1 (by norm_num)

/-! ### Unconditional verification of small cases -/

/-- Unconditional verification of Andrica's inequality for the first 101 primes:
`√p_{n+1} - √p_n < 1` for all `n ≤ 99` (i.e. up to `p_100 = 547`). -/

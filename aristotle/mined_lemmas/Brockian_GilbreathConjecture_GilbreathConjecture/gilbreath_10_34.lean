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
# The Gilbreath triangle: definition and explicit values

Auxiliary file for `Brockian.GilbreathConjecture`.  It sets up the Gilbreath triangle of the
primes and records the explicit values of its first eleven rows (as far as they are
determined by the first `45` primes).
-/

namespace Brockian.GilbreathConjecture

/-- Row `n`, entry `k` of the Gilbreath triangle of the prime numbers:
row `0` is the sequence of primes, and each later row consists of the absolute values of the
differences of consecutive entries of the previous row. -/

@[simp] theorem gilbreath_10_34 : gilbreath 10 34 = 2 := by simp [gilbreath_succ]

end Brockian.GilbreathConjecture

import Brockian.GilbreathTriangle

/-!
# Gilbreath Conjecture
Category: Brockian Conjecture
Target: Brockian.GilbreathConjecture.GilbreathConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The Gilbreath triangle of the primes is defined in `Brockian.GilbreathTriangle`:
row `0` is the sequence of primes `2, 3, 5, 7, 11, …` and

`gilbreath (n+1) k = |gilbreath n (k+1) - gilbreath n k|`.

Gilbreath's conjecture asserts that every row after row `0` begins with `1`.  It is an open
problem.  This file contains:

* the statement `GilbreathConjecture`;
* an unconditional parity invariant: for `n ≥ 1` the leading entry of row `n` is odd (hence
  nonzero) and all its other entries are even;
* Odlyzko's criterion, a conditional reduction: if a row starts with `1` followed by `m`
  entries in `{0, 2}`, then the next `m` rows also start with `1`; consequently the
  conjecture follows from the existence of arbitrarily far reaching such rows;
* an unconditional verification of the conjecture for all rows `1 ≤ n ≤ 44`.
-/

namespace Brockian.GilbreathConjecture

/-- **Gilbreath's conjecture**: every row of the Gilbreath triangle of the primes after
row `0` starts with the value `1`. -/

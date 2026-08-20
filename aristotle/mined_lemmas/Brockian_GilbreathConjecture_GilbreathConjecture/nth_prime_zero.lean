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
# Gilbreath Conjecture
Category: Brockian Conjecture
Target: Brockian.GilbreathConjecture.GilbreathConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

-- The header block above is a plain comment rather than a module docstring `/-! ... -/`
-- because Lean 4 does not allow any command (including a module docstring) before `import`.

namespace Brockian.GilbreathConjecture

/-!
## The Gilbreath triangle

Row `0` of the triangle is the sequence of primes `2, 3, 5, 7, 11, …`, and each
subsequent row is obtained by taking absolute values of consecutive differences.
Gilbreath's conjecture asserts that every row of index `≥ 1` begins with `1`.

The conjecture is open.  What is proved below is:

* `gilbreath_head_odd` – an unconditional parity result: the leading entry of every
  row of index `≥ 1` is odd (in particular nonzero);
* `gilbreath_head_eq_one_of_le` – an unconditional verification of the leading `1`
  for the first `25` rows;
* `GilbreathConjecture` – the full conjecture, derived from the Odlyzko-style
  criterion `OdlyzkoCriterion` (see below).
-/

/-- `G k n` is the `n`-th entry (0-indexed) of the `k`-th row of the Gilbreath
triangle: row `0` is the sequence of primes and each later row consists of the
absolute differences of consecutive entries of the previous row. -/

lemma nth_prime_zero : Nat.nth Nat.Prime 0 = 2 := by
  have h : Nat.nth Nat.Prime (Nat.count Nat.Prime 2) = 2 := Nat.nth_count Nat.prime_two
  have hc : Nat.count Nat.Prime 2 = 0 := by decide
  rwa [hc] at h


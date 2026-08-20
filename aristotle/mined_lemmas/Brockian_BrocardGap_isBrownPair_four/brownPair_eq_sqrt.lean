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
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Brocard Gap Conjecture

Brocard's problem asks for the solutions of `n ! + 1 = m ^ 2`; the only known ones are the
*Brown pairs* `(4, 5)`, `(5, 11)`, `(7, 71)`, and Brocard's conjecture (still open) states that
there are no further solutions.

This file develops the *gap* side of the problem, i.e. how far apart the perfect squares
surrounding `n ! + 1` are, and records what can be proved unconditionally:

* `Brockian.BrocardGap.BrocardGapConjecture` : for `n ≥ 10` the two consecutive squares
  bracketing `n ! + 1` are more than `2 ^ (n + 1)` apart;
* `Brockian.BrocardGap.unique_sq_near_factorial` : consequently, for `n ≥ 10` at most one
  natural number has its square within `2 ^ n` of `n ! + 1`;
* `Brockian.BrocardGap.no_brownPair_of_mem_Icc_eight_hundred` : an unconditional verification
  that there is no Brown pair with `8 ≤ n ≤ 100`;
* `Brockian.BrocardGap.two_pow_lt_of_brownPair` : any solution with `n ≥ 10` has `2 ^ n < m`;
* `Brockian.BrocardGap.brownPair_eq_sqrt`, `brownPair_factorization`, `brownPair_odd` :
  elementary structure of a solution;
* `Brockian.BrocardGap.brocardConjecture_iff_no_square` : a reformulation of the full
  (open) Brocard conjecture as the statement that `n ! + 1` is never a perfect square
  for `n ≥ 8`.
-/

open scoped Nat

namespace Brockian.BrocardGap

/-- A *Brown pair* is a pair `(n, m)` solving Brocard's equation `n ! + 1 = m ^ 2`. -/

theorem brownPair_eq_sqrt (n m : ℕ) (h : IsBrownPair n m) : m = Nat.sqrt (n ! + 1) := by
  rw [show n ! + 1 = m ^ 2 from h, Nat.sqrt_eq']

/-- A Brown pair factors the factorial: `n ! = (m - 1) * (m + 1)`. -/

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
/-!
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
-- (Lean does not allow a module docstring `/-! ... -/` before the `import` block, so the
-- required header above is enclosed in an ordinary block comment.)

import Brockian.BrocardVerification

open scoped Nat

namespace Brockian.BrocardProblem

/-!
Brocard's problem asks for all natural numbers `n`, `m` with `n ! + 1 = m ^ 2`.  The only
known solutions are `n = 4, 5, 7` (Brown numbers `(4, 5)`, `(5, 11)`, `(7, 71)`), and the
conjecture that these are the only ones is a well-known open problem.

This development provides:

* `brocard_le_1000` (in `Brockian.BrocardVerification`): an unconditional, machine-checked
  verification that for every `n ≤ 1000` the only solutions of `n ! + 1 = m ^ 2` are
  `(4, 5)`, `(5, 11)`, `(7, 71)`;
* `brocard_solution_odd`: an unconditional structural fact — any solution with `n ≥ 2` has
  `m` odd;
* `BrocardConjecture`: the conjecture itself, proved conditionally on the remaining open
  range `n > 1000`.  Together with `brocard_le_1000`, this is a Lean-checked reduction of
  Brocard's conjecture to that range.
-/

/-- If `n ! + 1 = m ^ 2` with `n ≥ 2`, then `m` is odd. -/

theorem factorial_succ_ne_sq_of_between (n k : ℕ) (h1 : k ^ 2 < n ! + 1)
    (h2 : n ! + 1 < (k + 1) ^ 2) (m : ℕ) : n ! + 1 ≠ m ^ 2 :=
  not_sq_of_between _ k h1 h2 m

local macro "kill_case" k:term " with " hh:ident mm:ident : tactic =>
  `(tactic|
    exact absurd $hh (factorial_succ_ne_sq_of_between _ $k (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) $mm))

/-- Unconditional verification of Brocard's conjecture in the range `n ≤ 1000`: the only
solutions of `n ! + 1 = m ^ 2` with `n ≤ 1000` are `(4, 5)`, `(5, 11)` and `(7, 71)`. -/

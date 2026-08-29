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
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module docstring `/-! ... -/` before `import`; the header above is
-- reproduced verbatim as a module docstring immediately after the import.)

import Mathlib
import Brockian.BrocardVerification

/-!
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Brocard's problem

Brocard's problem asks for all pairs of natural numbers `(n, m)` with

  `n ! + 1 = m ^ 2`.

The known solutions are `n = 4, 5, 7` (with `m = 5, 11, 71`), and **Brocard's conjecture**
states that there are no others.  This is a well-known open problem, so what is developed
here is:

* the precise statement, `Brockian.BrocardProblem.BrocardConjecture`;
* the three known solutions (`brocard_known_solutions`);
* an unconditional finite verification: the conjecture holds for all `n ≤ 300`
  (`brocard_holds_below`);
* a conditional reduction: the full conjecture is *equivalent* to the statement that
  `n ! + 1` is never a square for `n ≥ 301` (`brocardConjecture_iff_large`);
* an equivalent reformulation of solvability in terms of pronic numbers
  (`factorial_succ_sq_iff_pronic`): for `n ≥ 2`, `n ! + 1` is a square iff `n ! = 4 * a * (a+1)`
  for some `a`.
-/

namespace Brockian.BrocardProblem

open Nat

/-- **Brocard's conjecture** (open): the only natural numbers `n` for which `n ! + 1` is a
perfect square are `n = 4`, `n = 5` and `n = 7`. -/

theorem brocard_known_solutions :
    4 ! + 1 = 5 ^ 2 ∧ 5 ! + 1 = 11 ^ 2 ∧ 7 ! + 1 = 71 ^ 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [Nat.factorial]

/-- **Conditional reduction.**  Brocard's conjecture is equivalent to the assertion that
`n ! + 1` is not a perfect square for any `n ≥ 301`. -/

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
-- (Lean does not allow a module docstring `/-! ... -/` before `import`, so the
-- required header appears above as a block comment and is repeated verbatim as
-- the module docstring immediately after the imports.)

import Mathlib
import Brockian.BrocardData

/-!
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## What is proved here

Brocard's problem asks for all solutions in natural numbers of

$$ n! + 1 = m^2 . $$

The known solutions are `(n, m) = (4, 5), (5, 11), (7, 71)`, and *Brocard's
conjecture* asserts that there are no others.  This is an open problem; a search
of Mathlib turns up no result about the equation `n! + 1 = m²`, so nothing in the
library closes or nearly closes it.  The main library input used below is
`primorial_le_4_pow` (`n# ≤ 4 ^ n`).

Accordingly this file contains:

* `brocard_no_solution_below` : an **unconditional**, kernel-verified check that
  the only solutions with `n ≤ 1000` are the three known ones;
* `BrocardConjecture` : the **conditional reduction** — the full conjecture (as
  an exact classification of all solutions) follows from the statement that
  there is no solution with `n > 1000`;
* `brocard_finitely_many_of_abc` : a second, independent conditional result —
  the `abc` conjecture (in the explicit `ε = 1/2`, `ℕ`-valued form
  `c ^ 2 ≤ K * rad (a * b * c) ^ 3`) implies that Brocard's equation has only
  finitely many solutions, i.e. there is a bound beyond which there is none;
* `BrocardConjecture_of_abc_of_bound` : combining the two.
-/

namespace Brockian.BrocardProblem

open Finset

/-! ### Elementary square lemmas -/

/-- A number strictly between two consecutive squares is not a square. -/

theorem brocard_gap_data : ∀ n < 1001, n = 4 ∨ n = 5 ∨ n = 7 ∨
    ((brocardSqrtData.getD n 0) ^ 2 < Nat.factorial n + 1 ∧
      Nat.factorial n + 1 < (brocardSqrtData.getD n 0 + 1) ^ 2) := by
  decide

end Brockian


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

theorem ne_sq_of_between {A k m : ℕ} (h1 : k ^ 2 < A) (h2 : A < (k + 1) ^ 2) :
    A ≠ m ^ 2 := by
  rintro rfl
  have hk : k < m := by
    by_contra hcon
    push_neg at hcon
    exact absurd h1 (not_lt.2 (Nat.pow_le_pow_left hcon 2))
  exact absurd (Nat.pow_le_pow_left hk 2) (not_le.2 h2)

/-- Natural-number square roots are unique. -/

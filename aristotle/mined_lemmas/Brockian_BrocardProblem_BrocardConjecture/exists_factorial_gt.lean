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

theorem exists_factorial_gt (C : ℕ) :
    ∃ B, ∀ n, B ≤ n → C * 4096 ^ n < Nat.factorial n := by
  refine ⟨8192 + C * 4096 ^ 8192, fun n hn => ?_⟩
  set D := C * 4096 ^ 8192 with hD
  obtain ⟨j, rfl⟩ : ∃ j, n = 8192 + j := ⟨n - 8192, by omega⟩
  have hj : D ≤ j := by omega
  have hgrow := factorial_growth 8192 (le_refl _) j
  have hD2 : D < 2 ^ j :=
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) hj)
  have hpow : C * 4096 ^ (8192 + j) = D * 4096 ^ j := by rw [hD, pow_add]; ring
  calc C * 4096 ^ (8192 + j) = D * 4096 ^ j := hpow
    _ < 2 ^ j * 4096 ^ j :=
        Nat.mul_lt_mul_of_lt_of_le hD2 (le_refl _) (Nat.pow_pos (by norm_num))
    _ ≤ 2 ^ j * 4096 ^ j * Nat.factorial 8192 :=
        Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)
    _ ≤ Nat.factorial (8192 + j) := hgrow

/-! ### `abc` implies that Brocard's equation has only finitely many solutions -/

/-- Under `abc` with constant `K`, a solution of `n! + 1 = m ^ 2` forces
`n ! < K ^ 2 * 4096 ^ n`.

Indeed, applying `abc` to `1 + n! = m ^ 2` and bounding
`rad (n! · m²) ≤ rad (n!) · m ≤ 4 ^ n · m` gives `m ^ 4 ≤ K · 64 ^ n · m ^ 3`,
hence `m ≤ K · 64 ^ n` and `n! < m ^ 2 ≤ K ^ 2 · 4096 ^ n`. -/

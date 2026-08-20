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
-- (Lean requires `import` commands to precede every other command, including module
-- docstrings, so the header above is a plain comment and is repeated verbatim as the
-- module docstring below.)

import Mathlib
import Brockian.BrocardProblem.SmallCases

/-!
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Contents

Brocard's problem asks for all solutions of `n ! + 1 = m ^ 2`; the associated conjecture
(Brocard, Ramanujan) is that the only ones are `n = 4, 5, 7` (the *Brown numbers*).  The
conjecture is open.  This file contains:

* `Brockian.BrocardProblem.BrocardConjecture` — the statement of the conjecture;
* `Brockian.BrocardProblem.brown_numbers` — the three known solutions;
* `Brockian.BrocardProblem.brocard_below_301` — an unconditional verification of the
  conjecture for all `n < 301` (proved in `Brockian.BrocardProblem.SmallCases`);
* `Brockian.BrocardProblem.brocardConjecture_iff_ge_301` — the resulting reduction of the
  conjecture to the range `n ≥ 301`;
* `Brockian.BrocardProblem.brocard_finite_of_abc` — a conditional reduction: the `ε = 1/2`
  case of the `abc` conjecture (stated as `ABCConjectureHalf`) implies that Brocard's
  equation has only finitely many solutions.  This is the classical argument of Overholt.
-/

namespace Brockian
namespace BrocardProblem

open Finset Nat

/-! ### Brocard's conjecture -/

/-- **Brocard's conjecture**: the only natural numbers `n` for which `n ! + 1` is a perfect
square are `n = 4, 5, 7`. -/

theorem rad_factorial_le (n : ℕ) : rad (n !) ≤ 4 ^ n := by
  have hsub : (n !).primeFactors ⊆ (range (n + 1)).filter Nat.Prime := by
    intro p hp
    have hp1 := Nat.prime_of_mem_primeFactors hp
    have hp2 := Nat.dvd_of_mem_primeFactors hp
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := hp1.dvd_factorial.mp hp2; omega, hp1⟩
  calc rad (n !) ≤ primorial n :=
        Nat.le_of_dvd (primorial_pos n) (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
    _ ≤ 4 ^ n := primorial_le_4_pow n

/-! ### Factorials beat exponentials -/

/-- For fixed `D` and `B`, the inequality `n ! ≤ D * B ^ n` can only hold for `n` below an
explicit bound. -/

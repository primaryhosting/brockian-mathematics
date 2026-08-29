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
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean requires `import` commands to precede every other command, including
module doc comments, so the header above is a plain comment and is repeated as the
module docstring after the import below.)
-/

import Mathlib

/-!
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace QuasiperfectNumbers

open Finset

/-- A natural number `n` is *quasiperfect* if the sum of all its divisors equals `2 * n + 1`,
i.e. `σ n = 2n + 1`.  Whether a quasiperfect number exists is an open problem. -/

theorem not_quasiperfect_of_lt_two_hundred {n : ℕ} (hn : n < 200) : ¬ Quasiperfect n := by
  have h : ∀ m < 200, ¬ (0 < m ∧ ∑ d ∈ m.divisors, d = 2 * m + 1) := by decide
  exact h n hn

/-- **Conditional reduction for the existence of quasiperfect numbers.**

If a quasiperfect number exists at all, then one exists which is the square of an odd
number greater than `1`.  (Whether a quasiperfect number exists is an open problem.) -/

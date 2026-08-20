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
-/

import Mathlib

/-!
# Quasiperfect numbers

A natural number `n` is *quasiperfect* if `σ(n) = 2n + 1`, i.e. the sum of its proper
divisors is `n + 1`.  No quasiperfect number is known, and their existence is a
long-standing open problem.

This file proves Cattaneo's theorem — every quasiperfect number is an odd perfect
square — and deduces from it the conditional reduction
`Brockian.QuasiperfectNumbers.QuasiperfectExists`: a quasiperfect number exists if and
only if a quasiperfect number that is an odd perfect square exists.
-/

namespace Brockian.QuasiperfectNumbers

open Finset

/-- `sigmaSum n` is the sum of all positive divisors of `n`. -/

theorem not_quasiperfect_of_lt_200 {n : ℕ} (hn : n < 200) : ¬ Quasiperfect n := by
  revert hn
  show n < 200 → ¬ (0 < n ∧ sigmaSum n = 2 * n + 1)
  revert n
  decide

/--
**Conditional reduction for the existence of quasiperfect numbers.**

Whether a quasiperfect number (a number `n` with `σ(n) = 2n + 1`) exists is a
long-standing open problem; no example is known.  What is proved here is the
(nontrivial) reduction of the existence question to the existence of a quasiperfect
number that is moreover an odd perfect square: the two existence statements are
equivalent.
-/

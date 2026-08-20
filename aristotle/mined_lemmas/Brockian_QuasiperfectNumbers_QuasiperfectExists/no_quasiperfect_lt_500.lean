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

/-- A positive natural number `n` is *quasiperfect* if the sum of all of its divisors is
`2 * n + 1`, equivalently if the sum of its proper divisors is `n + 1`.

Whether a quasiperfect number exists is a longstanding open problem; no example is known,
and none can be small (see `no_quasiperfect_lt_500`). -/

theorem no_quasiperfect_lt_500 {n : ℕ} (hn : n < 500) : ¬ Quasiperfect n := by
  have key : ∀ m ∈ Finset.range 500, ∑ d ∈ m.divisors, d ≠ 2 * m + 1 := by decide
  intro h
  exact key n (Finset.mem_range.2 hn) h.2

/-! ### Main statement -/

/-- **Conditional reduction for the existence of quasiperfect numbers.**

Whether a quasiperfect number (a number `n` with `σ n = 2 * n + 1`) exists is a longstanding
open problem, so we record instead a Lean-checked reduction: a quasiperfect number exists if
and only if there is one that is at least `500`, is not a prime power, is a square or twice a
square, and has proper-divisor sum `n + 1`. -/

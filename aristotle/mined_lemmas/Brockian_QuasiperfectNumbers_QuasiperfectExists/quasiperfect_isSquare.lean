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

namespace Brockian.QuasiperfectNumbers

open Finset

/-- A natural number `n` is *quasiperfect* if the sum of its divisors equals `2 * n + 1`,
i.e. the sum of its proper divisors is `n + 1`. -/

theorem quasiperfect_isSquare {n : ℕ} (hn : 0 < n) (h : Quasiperfect n) : IsSquare n := by
  refine isSquare_of_odd_of_odd_sigma hn.ne' (quasiperfect_odd hn h) ?_
  rw [h]
  exact ⟨n, by ring⟩

/-- **Reduction of the existence question for quasiperfect numbers.**

A quasiperfect number exists if and only if there is an odd number `m > 1` whose square is
quasiperfect.  (Whether such a number exists is an open problem; this is a Lean-checked
equivalent reformulation, which in particular shows that any quasiperfect number is
necessarily the square of an odd number greater than `1`.) -/

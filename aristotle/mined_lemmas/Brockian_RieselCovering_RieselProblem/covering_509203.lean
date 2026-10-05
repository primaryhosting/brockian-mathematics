import Brockian.RieselCovering

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
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.RieselCovering

/-- A *Riesel number* is an odd natural number `k` such that `k * 2 ^ n - 1` is composite
(equivalently, not prime, since these numbers are `> 1`) for every `n ≥ 1`. -/

theorem covering_509203 (r : ℕ) (hr : r < 24) :
    ∃ p ∈ [3, 5, 7, 13, 17, 241], p ∣ 509203 * 2 ^ r - 1 := by
  revert hr
  revert r
  decide

/-- Each prime of the covering set has multiplicative order of `2` dividing `24`. -/

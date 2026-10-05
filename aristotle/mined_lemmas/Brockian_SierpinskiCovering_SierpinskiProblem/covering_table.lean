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

/-!
# Sierpinski Problem
Category: Brockian Conjecture
Target: Brockian.SierpinskiCovering.SierpinskiProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian
namespace SierpinskiCovering

/-- A *Sierpiński number* is an odd natural number `k` such that `k * 2 ^ n + 1` is composite
(never prime) for every `n ≥ 1`. -/

theorem covering_table :
    ∀ r < 36, ∃ p ∈ coveringPrimes, p ∣ 2 ^ 36 - 1 ∧ p ∣ 78557 * 2 ^ r + 1 := by
  decide

/-- Every number of the form `78557 * 2 ^ n + 1` has a nontrivial divisor from the
covering set, hence is not prime. -/

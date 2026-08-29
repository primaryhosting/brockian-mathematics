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
# Thabit Balance Identity
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers.Dynamics

/-- The Thabit-style candidate attached to the parameters `k` and `p`:
`m = (2 ^ k - 1) * (p + 2)`.  (The subtraction is harmless: `1 ≤ 2 ^ k`.) -/

def thabitCandidate (k p : ℕ) : ℕ := (2 ^ k - 1) * (p + 2)

/-- The delivered sigma criterion for the Thabit-style candidate, written in
subtraction-free form:  `σ₁(m) + (p + 1) = 2 ^ (k + 1) * (p + 1)`, i.e.
`σ₁(m) = (2 ^ (k + 1) - 1) * (p + 1)`. -/

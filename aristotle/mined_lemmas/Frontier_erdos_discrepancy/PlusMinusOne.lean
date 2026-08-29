/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- A `±1`-sequence: a function `f : ℕ → ℤ` taking only the values `1` and `-1`
on the positive integers. -/

def PlusMinusOne (f : ℕ → ℤ) : Prop := ∀ n : ℕ, 1 ≤ n → f n = 1 ∨ f n = -1

/-- The discrepancy of `f` along the homogeneous arithmetic progression of common
difference `d`, truncated at `n` terms: `|f d + f (2d) + ⋯ + f (nd)|`. -/

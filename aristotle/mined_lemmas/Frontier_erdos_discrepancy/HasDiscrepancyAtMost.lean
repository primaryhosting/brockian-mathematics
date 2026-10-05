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

/-- The partial sum of `f` along the homogeneous arithmetic progression of common
difference `d`: `apSum f d n = f d + f (2 * d) + ⋯ + f (n * d)`. -/

def HasDiscrepancyAtMost (f : ℕ → ℤ) (C : ℤ) : Prop :=
  ∀ d n : ℕ, 0 < d → |apSum f d n| ≤ C

/-- The Erdős discrepancy problem (theorem of Tao, 2015): every `±1` sequence has
unbounded discrepancy along homogeneous arithmetic progressions. -/

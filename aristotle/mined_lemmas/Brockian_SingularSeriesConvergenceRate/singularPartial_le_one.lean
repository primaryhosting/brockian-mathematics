/-
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- The local (Euler) factor of the twin-prime singular series at `p`:
`1 - 1/(p-1)^2` at odd primes, and `1` at all other natural numbers. -/

lemma singularPartial_le_one (N : ℕ) : singularPartial N ≤ 1 := by
  unfold singularPartial
  refine Finset.prod_le_one ?_ ?_
  · intro p hp; exact singularFactor_nonneg (Finset.mem_Ico.mp hp).1
  · intro p _; exact singularFactor_le_one p

/-- Weierstrass-type inequality: `∏ (1 - f i) ≥ 1 - ∑ f i`. -/

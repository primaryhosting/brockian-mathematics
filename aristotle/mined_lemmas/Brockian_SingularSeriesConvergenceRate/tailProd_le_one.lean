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

lemma tailProd_le_one (N M : ℕ) (hN : 2 ≤ N) :
    (∏ p ∈ Finset.Ico (N + 1) (M + 1), singularFactor p) ≤ 1 := by
  refine Finset.prod_le_one ?_ ?_
  · intro p hp
    exact singularFactor_nonneg (by have := (Finset.mem_Ico.mp hp).1; omega)
  · intro p _; exact singularFactor_le_one p

/-- The partial products are antitone. -/

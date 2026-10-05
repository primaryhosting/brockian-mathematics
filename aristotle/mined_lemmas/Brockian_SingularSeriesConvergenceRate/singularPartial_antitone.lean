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

lemma singularPartial_antitone : Antitone singularPartial := by
  intro N M hNM
  rcases Nat.lt_or_ge N 2 with hN | hN
  · have : singularPartial N = 1 := by
      unfold singularPartial
      rw [Finset.Ico_eq_empty (by omega), Finset.prod_empty]
    rw [this]
    exact singularPartial_le_one M
  · rw [singularPartial_split hN hNM]
    nlinarith [singularPartial_nonneg N, singularPartial_le_one N,
      tailProd_nonneg N M hN, tailProd_le_one N M hN]

/-- Key effective estimate: later partial products cannot drop far below earlier ones. -/

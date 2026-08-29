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
# Config Count Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.EquidistributionBVReduction

open Filter Finset

/-- The set of *configurations* of size `N`: pairs `(a, b)` of indices below `N`
whose total weight `a + b` still fits below the cut-off `N`.  This is the lattice
simplex that arises as the admissible index set in the bounded-variation reduction
step of an equidistribution argument. -/

lemma configCount_cast (N : ℕ) : (configCount N : ℝ) = (N : ℝ) * ((N : ℝ) + 1) / 2 := by
  have h : ((2 * configCount N : ℕ) : ℝ) = ((N * (N + 1) : ℕ) : ℝ) := by
    rw [two_mul_configCount]
  push_cast at h
  linarith

/-- **Main result.** The configuration count is asymptotic to its main term:
`configCount N / mainTerm N → 1` as `N → ∞`. -/

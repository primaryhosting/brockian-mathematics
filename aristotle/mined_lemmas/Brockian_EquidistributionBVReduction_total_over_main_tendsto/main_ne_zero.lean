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
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open Filter Topology

namespace Brockian.EquidistributionBVReduction

/-- The *main term* of the equidistribution / bounded-variation reduction: the
expected value `N * I` of the first `N` sampled values, where `I` is the mean
(integral) of the sampled function. -/

lemma main_ne_zero {I : ℝ} (hI : I ≠ 0) {N : ℕ} (hN : N ≠ 0) : main I N ≠ 0 :=
  mul_ne_zero (Nat.cast_ne_zero.mpr hN) hI

/-- Under a bounded-variation (Koksma-type) error bound `|total - main| ≤ C`, the
normalized error `(total N - main N) / main N` tends to `0`. -/

import Brockian.EquidistributionBVReduction

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

/-!
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Filter Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- The number of indices `n < N` for which the sequence value `x n` lies in `[0, a)`,
viewed as a real number.  This is the *total* count appearing in the bounded–variation
reduction step of an equidistribution argument. -/

theorem total_over_main_tendsto_of_discrepancy
    (x : ℕ → ℝ) (a : ℝ) (ha : 0 < a) {D : ℕ → ℝ}
    (hbound : ∀ᶠ N in atTop, discrepancy x a N ≤ D N)
    (hD : Tendsto D atTop (𝓝 0)) :
    Tendsto (fun N => count x a N / mainTerm a N) atTop (𝓝 1) := by
  refine total_over_main_tendsto x a ha ?_
  refine squeeze_zero_norm' ?_ hD
  filter_upwards [hbound] with N hN
  simpa [discrepancy, Real.norm_eq_abs] using hN

/-- The count never exceeds the number of terms considered. -/

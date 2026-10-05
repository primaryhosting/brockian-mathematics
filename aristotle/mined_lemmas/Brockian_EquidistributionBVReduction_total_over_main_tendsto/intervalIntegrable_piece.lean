import Mathlib

/-!
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
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

set_option grind.warning false

namespace Brockian
namespace EquidistributionBVReduction

open Filter Finset

/-- The `N`-th equidistributed sample sum of `f`: the total of the values of `f` at the
`N` equidistributed sample points `0/N, 1/N, …, (N-1)/N` of the unit interval. -/

lemma intervalIntegrable_piece (hp : MonotoneOn p (Set.Icc (0:ℝ) 1)) {N k : ℕ} (hk : k < N) :
    IntervalIntegrable p MeasureTheory.volume ((k : ℝ) / N) (((k : ℝ) + 1) / N) :=
  MonotoneOn.intervalIntegrable (hp.mono (uIcc_subset_unit hk))

/-- The integral over `[0,1]` splits as the sum of the integrals over the pieces of the
uniform partition. -/

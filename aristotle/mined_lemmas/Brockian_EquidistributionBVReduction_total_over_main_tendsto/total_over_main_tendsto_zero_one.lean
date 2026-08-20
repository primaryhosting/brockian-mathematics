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

theorem total_over_main_tendsto_zero_one :
    Tendsto (fun N => count (fun _ => (0 : ℝ)) 1 N / mainTerm 1 N) atTop (𝓝 1) :=
  total_over_main_tendsto _ 1 one_pos discrepancy_zero_one_tendsto

/-!
### A nontrivial equidistributed example

The two-periodic sequence `evenSeq n = if n even then 0 else 1/2` hits the interval
`[0, 1/2)` exactly at the even indices, so its counting function has discrepancy `O(1/N)`
for the density `a = 1/2`.  This gives an instance of `total_over_main_tendsto` with
`a ≠ 1`.
-/

/-- The two-periodic sequence taking the value `0` at even indices and `1/2` at odd ones. -/

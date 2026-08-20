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

theorem ratio_tendsto_one_of_sub_tendsto_zero
    {f : ℕ → ℝ} {a : ℝ} (ha : a ≠ 0)
    (h : Tendsto (fun N => f N - a) atTop (𝓝 0)) :
    Tendsto (fun N => f N / a) atTop (𝓝 1) := by
  have hf : Tendsto f atTop (𝓝 a) := by
    have := h.add (tendsto_const_nhds (x := a) (f := (atTop : Filter ℕ)))
    simpa using this
  have := hf.div_const a
  rwa [div_self ha] at this

/-- **Total over main tends to one.**

If the normalized counting function `count x a N / N` of the sequence `x` converges to the
density `a` of the interval `[0, a)` (the equidistribution hypothesis, which in the
bounded–variation reduction is supplied by the discrepancy estimate), then the ratio of the
total count to the main term `N * a` tends to `1`.

Previously this was assumed as a named hypothesis; it is now unconditional given the
equidistribution input. -/

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

import Mathlib
/-!
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Set MeasureTheory
open scoped BigOperators Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- The empirical frequency with which the first `N` terms of the sequence `x`
land in the interval `[a, b)`. -/

def UniformlyDistributed (x : ℕ → ℝ) : Prop :=
  (∀ n, x n ∈ Set.Ico (0 : ℝ) 1) ∧
    ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → Tendsto (freq x a b) atTop (𝓝 (b - a))

/-- The step function on `[0,1)` which takes the value `c i` on the `i`-th interval
`[i / k, (i+1) / k)` of the uniform partition of `[0, 1)` into `k` pieces. -/

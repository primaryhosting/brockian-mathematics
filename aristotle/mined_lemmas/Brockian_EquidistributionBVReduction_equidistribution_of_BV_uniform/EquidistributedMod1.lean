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

open scoped BigOperators
open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace Brockian.EquidistributionBVReduction

/-- The (right-continuous) step function jumping from `0` to `1` at `c`. -/

def EquidistributedMod1 (x : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    Tendsto (fun N : ℕ =>
        (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) / N)
      atTop (𝓝 (b - a))

/-- The "BV test-function" hypothesis: the Birkhoff-type averages of the sequence along every
integrable function of bounded variation on `[0, 1]` converge to the integral of that function
with respect to the uniform (Lebesgue) measure on `[0, 1]`. -/

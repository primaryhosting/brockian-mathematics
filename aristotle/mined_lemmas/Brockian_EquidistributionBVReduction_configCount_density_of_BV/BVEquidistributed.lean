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
# Config Count Density Of BV
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_density_of_BV
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators ENNReal
open Set Filter MeasureTheory

namespace Brockian
namespace EquidistributionBVReduction

/-! ## Variation of a difference -/

/-- The variation of a difference of two real-valued functions is at most the sum of the
variations. -/

def BVEquidistributed (x : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, BoundedVariationOn f (Set.Icc (0 : ℝ) 1) →
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (Int.fract (x n))) / N) atTop
      (nhds (∫ t in (0 : ℝ)..1, f t))

/-- Rewriting a configuration count as a Birkhoff sum of an indicator. -/

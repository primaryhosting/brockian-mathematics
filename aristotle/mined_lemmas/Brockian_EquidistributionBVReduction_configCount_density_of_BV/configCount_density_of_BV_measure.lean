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
# Config Count Density Of BV
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_density_of_BV
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory Filter Topology Set

namespace Brockian.EquidistributionBVReduction

open scoped Classical in
/-- `configCount x A N` is the number of indices `n < N` whose orbit point `x n`,
reduced mod `1`, lands in the configuration set `A`. -/

theorem configCount_density_of_BV_measure (x : ℕ → ℝ) (hx : EquidistributedMod1 x) (A : Set ℝ)
    (hAm : MeasurableSet A)
    (hA : BoundedVariationOn (A.indicator (fun _ => (1:ℝ))) (Set.Icc (0:ℝ) 1)) :
    Tendsto (fun N : ℕ => (configCount x A N : ℝ) / N)
      atTop (𝓝 (volume.real (A ∩ Set.Ioc (0:ℝ) 1))) := by
  have hint : (∫ t in (0:ℝ)..1, A.indicator (fun _ => (1:ℝ)) t)
      = volume.real (A ∩ Set.Ioc (0:ℝ) 1) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      show (fun t => A.indicator (fun _ => (1:ℝ)) t) = A.indicator 1 from rfl,
      MeasureTheory.integral_indicator_one hAm, measureReal_restrict_apply hAm]
  simpa [hint] using configCount_density_of_BV x hx A hA

/-! ### Sanity check: the hypotheses are non-vacuous -/


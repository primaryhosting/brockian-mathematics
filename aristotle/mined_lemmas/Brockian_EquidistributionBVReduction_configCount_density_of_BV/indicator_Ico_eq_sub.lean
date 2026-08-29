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

theorem indicator_Ico_eq_sub {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    Set.indicator (Set.Ico a b) (fun _ => (1 : ℝ)) t =
      Set.indicator (Set.Ici a) (fun _ => (1 : ℝ)) t -
        Set.indicator (Set.Ici b) (fun _ => (1 : ℝ)) t := by
  by_cases ha : a ≤ t <;> by_cases hb : b ≤ t <;>
    simp [Set.indicator_apply, ha, hb]
  all_goals linarith

/-- The indicator of an interval `[a, b)` has bounded variation on `[0, 1]`. -/

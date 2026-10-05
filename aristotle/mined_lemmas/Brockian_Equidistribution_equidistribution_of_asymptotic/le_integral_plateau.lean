import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
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

namespace Brockian.Equidistribution

open MeasureTheory Filter Topology Metric Finset

noncomputable section

local notation "𝕋" => AddCircle (1 : ℝ)

/-! ### Cesàro averages along a sequence -/

/-- The Cesàro average of a function `f` on the circle `ℝ/ℤ` along the first `N` terms of a
real sequence `x`. -/

lemma le_integral_plateau (c : 𝕋) (s ε : ℝ) (hε : 0 < ε) (hs : 0 ≤ s) (h1 : 2 * s ≤ 1) :
    2 * s ≤ ∫ z, plateau c s ε z := by
  have hind : Integrable ((closedBall c s).indicator (fun _ => (1 : ℝ)))
      (volume : Measure 𝕋) := (integrable_const (1 : ℝ)).indicator measurableSet_closedBall
  have hle : ∀ z, (closedBall c s).indicator (fun _ => (1 : ℝ)) z ≤ plateau c s ε z := by
    intro z
    by_cases hz : z ∈ closedBall c s
    · rw [Set.indicator_of_mem hz, plateau_eq_one hε (mem_closedBall.mp hz)]
    · rw [Set.indicator_of_notMem hz]; exact plateau_nonneg _ _ _ _
  calc 2 * s = (volume : Measure 𝕋).real (closedBall c s) := by
        rw [measureReal_def, AddCircle.volume_closedBall, min_eq_right h1,
          ENNReal.toReal_ofReal (by linarith)]
    _ = ∫ z, (closedBall c s).indicator (fun _ => (1 : ℝ)) z := by
        rw [integral_indicator_const _ measurableSet_closedBall]; simp
    _ ≤ ∫ z, plateau c s ε z := integral_mono hind (integrable_cmR _) hle

/-! ### Counting and the main theorem -/

/-- The number of indices `n < N` whose fractional part lands in `[a, b)`. -/

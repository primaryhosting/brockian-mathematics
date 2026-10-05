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

lemma integral_plateau_le (c : 𝕋) (s ε : ℝ) (hε : 0 < ε) (hs : 0 ≤ s + ε) :
    (∫ z, plateau c s ε z) ≤ 2 * (s + ε) := by
  have hind : Integrable ((closedBall c (s + ε)).indicator (fun _ => (1 : ℝ)))
      (volume : Measure 𝕋) := (integrable_const (1 : ℝ)).indicator measurableSet_closedBall
  have hle : ∀ z, plateau c s ε z ≤ (closedBall c (s + ε)).indicator (fun _ => (1 : ℝ)) z := by
    intro z
    by_cases hz : z ∈ closedBall c (s + ε)
    · rw [Set.indicator_of_mem hz]; exact plateau_le_one _ _ _ _
    · rw [Set.indicator_of_notMem hz]
      rw [mem_closedBall, not_le] at hz
      exact le_of_eq (plateau_eq_zero hε hz.le)
  calc (∫ z, plateau c s ε z)
      ≤ ∫ z, (closedBall c (s + ε)).indicator (fun _ => (1 : ℝ)) z :=
        integral_mono (integrable_cmR _) hind hle
    _ = (volume : Measure 𝕋).real (closedBall c (s + ε)) := by
        rw [integral_indicator_const _ measurableSet_closedBall]; simp
    _ ≤ 2 * (s + ε) := by
        rw [measureReal_def, AddCircle.volume_closedBall]
        rcases le_total 1 (2 * (s + ε)) with h1 | h1
        · rw [min_eq_left h1, ENNReal.toReal_ofReal zero_le_one]; linarith
        · rw [min_eq_right h1, ENNReal.toReal_ofReal (by linarith)]


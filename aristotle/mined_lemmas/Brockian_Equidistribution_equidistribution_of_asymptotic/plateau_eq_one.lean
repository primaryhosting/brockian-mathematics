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

lemma plateau_eq_one {c : 𝕋} {s ε : ℝ} (hε : 0 < ε) {z : 𝕋} (hz : dist z c ≤ s) :
    plateau c s ε z = 1 := by
  simp only [plateau, ContinuousMap.coe_mk]
  have h : (1 : ℝ) ≤ (s + ε - dist z c) / ε := by rw [le_div_iff₀ hε]; linarith
  exact min_eq_left (le_max_of_le_right h)


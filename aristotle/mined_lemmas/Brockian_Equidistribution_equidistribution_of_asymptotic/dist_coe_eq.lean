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

lemma dist_coe_eq (y m : ℝ) : dist ((y : ℝ) : 𝕋) ((m : ℝ) : 𝕋) = ‖((y - m : ℝ) : 𝕋)‖ := by
  rw [dist_eq_norm, ← AddCircle.coe_sub]

/-- If the fractional part of `y` lies in `[a, b)` then, on the circle, `y` is within `(b-a)/2`
of the midpoint of the arc. -/

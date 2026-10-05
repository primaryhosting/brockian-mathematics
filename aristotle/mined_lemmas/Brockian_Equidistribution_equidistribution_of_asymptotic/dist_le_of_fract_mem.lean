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

lemma dist_le_of_fract_mem {a b y : ℝ} (h : Int.fract y ∈ Set.Ico a b) :
    dist ((y : ℝ) : 𝕋) (((a + b) / 2 : ℝ) : 𝕋) ≤ (b - a) / 2 := by
  rw [dist_coe_eq]
  refine le_trans (norm_coe_le_abs_sub_int _ ⌊y⌋) ?_
  have hy : y - (a + b) / 2 - ⌊y⌋ = Int.fract y - (a + b) / 2 := by
    rw [← Int.self_sub_floor y]; ring
  rw [hy, abs_le]
  obtain ⟨h1, h2⟩ := h
  exact ⟨by linarith, by linarith⟩

/-- Conversely, points of the open arc have fractional part in `[a, b)`. -/

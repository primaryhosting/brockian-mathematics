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

lemma fract_mem_of_dist_lt {a b y : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (h : dist ((y : ℝ) : 𝕋) (((a + b) / 2 : ℝ) : 𝕋) < (b - a) / 2) :
    Int.fract y ∈ Set.Ico a b := by
  rw [dist_coe_eq] at h
  obtain ⟨k, hk⟩ := exists_int_of_norm_lt h
  rw [abs_lt] at hk
  have h1 : a < y - k := by linarith [hk.1]
  have h2 : y - k < b := by linarith [hk.2]
  have hfr : Int.fract y = y - k := by
    have hs : Int.fract (y - k) = y - k := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    rw [← hs, Int.fract_sub_intCast]
  rw [hfr]
  exact ⟨le_of_lt h1, h2⟩

/-! ### Continuous approximations of arc indicators -/

/-- A continuous "plateau" function on the circle: it equals `1` on `closedBall c s` and
vanishes outside `closedBall c (s + ε)`. -/

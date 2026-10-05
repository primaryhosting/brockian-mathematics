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

lemma isClosed_equidist (x : ℕ → ℝ) : IsClosed (Equidist x : Set C(𝕋, ℂ)) := by
  apply isClosed_of_closure_subset
  intro f hf
  show Tendsto (cavg x f) atTop (𝓝 (∫ z, f z))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp hf (ε / 3) (by positivity)
  rw [SetLike.mem_coe, mem_equidist_iff] at hg
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hg (ε / 3) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  have e1 : ‖cavg x f N - cavg x g N‖ ≤ ‖f - g‖ := by
    rw [← cavg_sub]
    simpa [ContinuousMap.coe_sub] using norm_cavg_le x (f - g) N
  have e3 : ‖(∫ z, g z) - ∫ z, f z‖ ≤ ‖f - g‖ := by
    rw [← integral_sub (integrable_cm g) (integrable_cm f)]
    have h := norm_integral_le_norm (g - f)
    simp only [ContinuousMap.coe_sub, Pi.sub_apply] at h
    rw [show ‖f - g‖ = ‖g - f‖ from norm_sub_rev f g]
    exact h
  have hd : ‖f - g‖ < ε / 3 := by rw [← dist_eq_norm]; exact hfg
  calc dist (cavg x f N) (∫ z, f z)
      ≤ dist (cavg x f N) (cavg x g N) + dist (cavg x g N) (∫ z, g z)
        + dist (∫ z, g z) (∫ z, f z) := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · rw [dist_eq_norm]; exact lt_of_le_of_lt e1 hd
        · exact hN₀ N hN
        · rw [dist_eq_norm]; exact lt_of_le_of_lt e3 hd
    _ = ε := by ring

/-- The integral of a Fourier monomial over the circle. -/

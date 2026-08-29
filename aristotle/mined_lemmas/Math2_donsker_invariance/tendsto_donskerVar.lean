/-
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Math2

/-- The linearly interpolated, rescaled random walk
`W_n(t) = (S_{⌊nt⌋} + (nt - ⌊nt⌋) X_{⌊nt⌋}) / √n`, where `S_m = X_0 + ⋯ + X_{m-1}`.
This is the classical Donsker polygonal process associated to the steps `X`. -/

lemma tendsto_donskerVar {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ ↦ ((donskerVar n t : ℝ≥0) : ℝ)) atTop (𝓝 t) := by
  have hlim : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ ↦ t - (n : ℝ)⁻¹) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.sub hlim
  have hr : Tendsto (fun n : ℕ ↦ t + (n : ℝ)⁻¹) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.add hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hr ?_ ?_ <;>
    filter_upwards [eventually_gt_atTop 0] with n hn
  · have hnpos : (0:ℝ) < n := by exact_mod_cast hn
    have hinv : (n : ℝ) * ((n : ℝ)⁻¹) = 1 := by field_simp
    have hfl : (⌊(n : ℝ) * t⌋₊ : ℝ) ≤ (n : ℝ) * t := Nat.floor_le (by positivity)
    have hfl2 : (n : ℝ) * t < (⌊(n : ℝ) * t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [donskerVar, Real.coe_toNNReal _ (by positivity), le_div_iff₀ hnpos]
    nlinarith [sq_nonneg ((n : ℝ) * t - ⌊(n : ℝ) * t⌋₊)]
  · have hnpos : (0:ℝ) < n := by exact_mod_cast hn
    have hinv : (n : ℝ) * ((n : ℝ)⁻¹) = 1 := by field_simp
    have hfl : (⌊(n : ℝ) * t⌋₊ : ℝ) ≤ (n : ℝ) * t := Nat.floor_le (by positivity)
    have hfl2 : (n : ℝ) * t < (⌊(n : ℝ) * t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [donskerVar, Real.coe_toNNReal _ (by positivity), div_le_iff₀ hnpos]
    have h1 : ((n : ℝ) * t - ⌊(n : ℝ) * t⌋₊) ^ 2 ≤ 1 := by nlinarith
    nlinarith


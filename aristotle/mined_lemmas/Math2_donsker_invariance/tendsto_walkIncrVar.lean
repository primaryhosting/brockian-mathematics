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

lemma tendsto_walkIncrVar {u : ℕ → ℝ} (hu : Monotone u) (hu0 : 0 ≤ u 0) (j : ℕ) :
    Tendsto (fun n : ℕ ↦ ((walkIncrVar u n j : ℝ≥0) : ℝ)) atTop (𝓝 (u (j + 1) - u j)) := by
  have huj : 0 ≤ u j := le_trans hu0 (hu (Nat.zero_le _))
  have huj1 : u j ≤ u (j + 1) := hu (Nat.le_succ _)
  have hlim : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ ↦ (u (j + 1) - u j) - (n : ℝ)⁻¹) atTop (𝓝 (u (j + 1) - u j)) := by
    simpa using tendsto_const_nhds.sub hlim
  have hr : Tendsto (fun n : ℕ ↦ (u (j + 1) - u j) + (n : ℝ)⁻¹) atTop (𝓝 (u (j + 1) - u j)) := by
    simpa using tendsto_const_nhds.add hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hr ?_ ?_ <;>
    filter_upwards [eventually_gt_atTop 0] with n hn
  all_goals {
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hinv : (n : ℝ) * ((n : ℝ)⁻¹) = 1 := by field_simp
    have hab : ⌊(n : ℝ) * u j⌋₊ ≤ ⌊(n : ℝ) * u (j + 1)⌋₊ := Nat.floor_le_floor (by nlinarith)
    have h1 : (⌊(n : ℝ) * u j⌋₊ : ℝ) ≤ (n : ℝ) * u j := Nat.floor_le (by nlinarith)
    have h2 : (n : ℝ) * u j < (⌊(n : ℝ) * u j⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : (⌊(n : ℝ) * u (j + 1)⌋₊ : ℝ) ≤ (n : ℝ) * u (j + 1) := Nat.floor_le (by nlinarith)
    have h4 : (n : ℝ) * u (j + 1) < (⌊(n : ℝ) * u (j + 1)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [walkIncrVar, Real.coe_toNNReal _ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),
      Nat.cast_sub hab]
    first
      | (rw [le_div_iff₀ hnpos]; nlinarith)
      | (rw [div_le_iff₀ hnpos]; nlinarith) }

/-- The vector of values of the rescaled walk is the vector of partial sums of its increments. -/

/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set MeasureTheory intervalIntegral
open scoped Real

namespace Math2

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

lemma stepIntegral_bound {f : ℝ → ℝ} (hf : Continuous f) {n : ℕ} (hn : 0 < n) {c : ℝ}
    (hunif : ∀ x ∈ Icc 0 Real.pi, ∀ y ∈ Icc 0 Real.pi, |x - y| ≤ Real.pi / n → |f x - f y| ≤ c) :
    |(f Real.pi + ∑ j ∈ Finset.range n, (f (grid n j) - f (grid n (j + 1)))
          * (∫ x in (0 : ℝ)..grid n j, satoTateDensity x))
        - ∫ x in (0 : ℝ)..Real.pi, satoTateDensity x * f x| ≤ c := by
  have hpn : 0 ≤ Real.pi / n := by have := Real.pi_pos.le; positivity
  set M : ℕ → ℝ := fun j => ∫ x in (0 : ℝ)..grid n j, satoTateDensity x with hM
  set g : ℕ → ℝ := fun j => f (grid n j) with hg
  have hM0 : M 0 = 0 := by simp [hM, grid_zero]
  have hMn : M n = 1 := by
    rw [hM]; simp only; rw [grid_self hn]; exact integral_satoTateDensity
  have hgn : g n = f Real.pi := by rw [hg]; simp only [grid_self hn]
  have habel := abel_sum_aux g M n hM0
  have hcell : ∀ j, M (j + 1) - M j = ∫ x in (grid n j)..(grid n (j + 1)), satoTateDensity x := by
    intro j
    have h := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (a := (0 : ℝ)) (b := grid n j) (c := grid n (j + 1))
      (continuous_satoTateDensity.intervalIntegrable _ _)
      (continuous_satoTateDensity.intervalIntegrable _ _)
    simp only [hM]
    linarith [h]
  have hB : (f Real.pi + ∑ j ∈ Finset.range n, (g j - g (j + 1)) * M j)
      = ∑ j ∈ Finset.range n, g (j + 1) * (M (j + 1) - M j) := by
    rw [← habel, hgn, hMn]; ring
  rw [show (∑ j ∈ Finset.range n, (f (grid n j) - f (grid n (j + 1))) * M j)
      = ∑ j ∈ Finset.range n, (g j - g (j + 1)) * M j from rfl, hB]
  have hsplit : (∫ x in (0 : ℝ)..Real.pi, satoTateDensity x * f x)
      = ∑ j ∈ Finset.range n, ∫ x in (grid n j)..(grid n (j + 1)), satoTateDensity x * f x := by
    rw [integral_split_grid (grid n) (fun x => satoTateDensity x * f x)
      (continuous_satoTateDensity.mul hf) n, grid_zero, grid_self hn]
  rw [hsplit, ← Finset.sum_sub_distrib]
  calc |∑ j ∈ Finset.range n, (g (j + 1) * (M (j + 1) - M j)
          - ∫ x in (grid n j)..(grid n (j + 1)), satoTateDensity x * f x)|
      ≤ ∑ j ∈ Finset.range n, |g (j + 1) * (M (j + 1) - M j)
          - ∫ x in (grid n j)..(grid n (j + 1)), satoTateDensity x * f x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n, c * ∫ x in (grid n j)..(grid n (j + 1)), satoTateDensity x := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [Finset.mem_range] at hj
        rw [hcell j]
        refine cell_bound (grid_mono (Nat.le_succ j)) hf ?_
        intro x hx
        have hx1 : x ∈ Icc 0 Real.pi :=
          ⟨le_trans (grid_nonneg n j) hx.1, le_trans hx.2 (grid_mem hn hj).2⟩
        refine hunif _ (grid_mem hn hj) _ hx1 ?_
        rw [abs_le]
        have h1 := hx.1
        have h2 := hx.2
        have h3 := grid_succ_sub hn j
        constructor <;> linarith
    _ = c * ∑ j ∈ Finset.range n, ∫ x in (grid n j)..(grid n (j + 1)), satoTateDensity x := by
        rw [Finset.mul_sum]
    _ = c := by
        rw [integral_split_grid (grid n) satoTateDensity continuous_satoTateDensity n,
          grid_zero, grid_self hn, integral_satoTateDensity, mul_one]



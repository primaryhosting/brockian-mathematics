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

open Filter Real MeasureTheory
open scoped Topology BigOperators Classical

namespace Math2

/-! ## The Sato–Tate distribution -/

/-- The Sato–Tate density `(2/π) sin²θ` on `[0, π]`. -/

lemma integral_trap_inner_ge {a b δ : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π) :
    (stCDF b - stCDF a) - (4 / π) * δ
      ≤ ∫ x in (0:ℝ)..π, trap a b δ x * stDensity x := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  set f : ℝ → ℝ := fun x => trap a b δ x * stDensity x with hf
  have hcont : Continuous f := (continuous_trap _ _ _).mul continuous_stDensity
  have hfnonneg : ∀ x, 0 ≤ f x := fun x =>
    mul_nonneg (trap_nonneg _ _ _ _) (stDensity_nonneg x)
  rcases lt_or_ge (b - δ) (a + δ) with hcase | hcase
  · have h0 : 0 ≤ ∫ x in (0:ℝ)..π, f x :=
      intervalIntegral.integral_nonneg hpi.le (fun x _ => hfnonneg x)
    have hsub := stCDF_sub_le hab
    have hle : (2 / π) * (b - a) ≤ (2 / π) * (2 * δ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have heq : (2 / π) * (2 * δ) = (4 / π) * δ := by ring
    linarith
  · have hac : 0 ≤ a + δ := by linarith
    have hdpi : b - δ ≤ π := by linarith
    have hsplit : (∫ x in (0:ℝ)..(a + δ), f x) + (∫ x in (a + δ)..(b - δ), f x)
        + (∫ x in (b - δ)..π, f x) = ∫ x in (0:ℝ)..π, f x := by
      rw [intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _),
        intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
    have h1 : 0 ≤ ∫ x in (0:ℝ)..(a + δ), f x :=
      intervalIntegral.integral_nonneg hac (fun x _ => hfnonneg x)
    have h3 : 0 ≤ ∫ x in (b - δ)..π, f x :=
      intervalIntegral.integral_nonneg hdpi (fun x _ => hfnonneg x)
    have h2 : (∫ x in (a + δ)..(b - δ), f x) = stCDF (b - δ) - stCDF (a + δ) := by
      rw [← integral_stDensity]
      refine intervalIntegral.integral_congr ?_
      intro x hx
      rw [Set.uIcc_of_le hcase] at hx
      simp only [hf]
      rw [trap_eq_one hδ hx.1 hx.2, one_mul]
    have e1 : stCDF b - stCDF (b - δ) ≤ (2 / π) * δ := by
      have := stCDF_sub_le (show b - δ ≤ b by linarith)
      have hbd : b - (b - δ) = δ := by ring
      rw [hbd] at this
      exact this
    have e2 : stCDF (a + δ) - stCDF a ≤ (2 / π) * δ := by
      have := stCDF_sub_le (show a ≤ a + δ by linarith)
      have had : a + δ - a = δ := by ring
      rw [had] at this
      exact this
    have esum : (2 / π) * δ + (2 / π) * δ = (4 / π) * δ := by ring
    linarith

/-! ## From convergence against continuous test functions to counting in intervals -/


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

lemma STAverage_of_continuous {θ : ℕ → ℝ} (hθ : ∀ p, θ p ∈ Set.Icc (0:ℝ) π)
    (hmom : ∀ n : ℕ, 1 ≤ n → Tendsto (primeAvg θ (UBasis n)) atTop (𝓝 0))
    {f : ℝ → ℝ} (hf : Continuous f) : STAverage θ f := by
  rw [STAverage, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn (-1) 1
    (fun y => f (Real.arccos y)) (by fun_prop) (ε / 3) (by linarith)
  set g : ℝ → ℝ := fun x => P.eval (Real.cos x) with hgdef
  have hgcont : Continuous g := by
    exact (P.continuous_aeval).comp Real.continuous_cos
  have hgood : STAverage θ g := STAverage_of_mem_USpan hmom (polyCos_mem_USpan P)
  have hclose : ∀ x ∈ Set.Icc (0:ℝ) π, |f x - g x| ≤ ε / 3 := by
    intro x hx
    have h1 : Real.cos x ∈ Set.Icc (-1:ℝ) 1 := ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩
    have h2 := hP (Real.cos x) h1
    rw [Real.arccos_cos hx.1 hx.2] at h2
    rw [abs_sub_comm]
    exact h2.le
  have hb1 : ∀ X, |primeAvg θ f X - primeAvg θ g X| ≤ ε / 3 := by
    intro X
    rw [← primeAvg_sub]
    exact abs_primeAvg_le hθ (by linarith) (fun x hx => hclose x hx) X
  have hb2 : |(∫ x in (0:ℝ)..π, f x * stDensity x) - ∫ x in (0:ℝ)..π, g x * stDensity x|
      ≤ ε / 3 := by
    have hsub : (∫ x in (0:ℝ)..π, (f x - g x) * stDensity x)
        = (∫ x in (0:ℝ)..π, f x * stDensity x) - ∫ x in (0:ℝ)..π, g x * stDensity x := by
      have hc : (∫ x in (0:ℝ)..π, (f x - g x) * stDensity x)
          = ∫ x in (0:ℝ)..π, (f x * stDensity x - g x * stDensity x) := by
        refine intervalIntegral.integral_congr ?_
        intro x _
        simp [sub_mul]
      rw [hc]
      exact intervalIntegral.integral_sub
        ((hf.mul continuous_stDensity).intervalIntegrable _ _)
        ((hgcont.mul continuous_stDensity).intervalIntegrable _ _)
    rw [← hsub]
    exact abs_integral_le_of_bound (hf.sub hgcont) hclose
  obtain ⟨X0, hX0⟩ := Metric.tendsto_atTop.1 hgood (ε / 3) (by linarith)
  refine ⟨X0, fun X hX => ?_⟩
  have h3 := hX0 X hX
  rw [Real.dist_eq] at h3 ⊢
  have h1 := abs_le.1 (hb1 X)
  have h2 := abs_le.1 hb2
  have h4 := abs_lt.1 h3
  rw [abs_lt]
  constructor <;> linarith

/-! ## Frobenius angles of an elliptic curve -/

/-- The number of affine points of the Weierstrass curve `y² = x³ + A x + B` over `ZMod p`. -/

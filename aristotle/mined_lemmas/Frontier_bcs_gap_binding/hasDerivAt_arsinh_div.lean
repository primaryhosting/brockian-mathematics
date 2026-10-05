/-
/-!
# Bcs Gap Binding
Category: Frontier Physics
Target: Frontier.bcs_gap_binding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
import Mathlib

namespace Frontier

open Real intervalIntegral

/-- The BCS kernel `ξ ↦ 1 / √(ξ² + Δ²)` is continuous when `Δ ≠ 0`. -/

lemma hasDerivAt_arsinh_div {Δ : ℝ} (hΔ : 0 < Δ) (ξ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.arsinh (x / Δ))
      (1 / Real.sqrt (ξ ^ 2 + Δ ^ 2)) ξ := by
  have h1 : HasDerivAt (fun x : ℝ => x / Δ) (1 / Δ) ξ := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id ξ).mul_const Δ⁻¹
  have h2 := (Real.hasDerivAt_arsinh (ξ / Δ)).comp ξ h1
  have h3 : Real.sqrt (ξ ^ 2 + Δ ^ 2) = Real.sqrt (1 + (ξ / Δ) ^ 2) * Δ := by
    rw [show ξ ^ 2 + Δ ^ 2 = (1 + (ξ / Δ) ^ 2) * Δ ^ 2 by field_simp; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hΔ.le]
  have hspos : 0 < Real.sqrt (1 + (ξ / Δ) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hkey : (Real.sqrt (1 + (ξ / Δ) ^ 2))⁻¹ * Δ⁻¹
      = (Real.sqrt (ξ ^ 2 + Δ ^ 2))⁻¹ := by
    rw [h3]; field_simp
  simpa [Function.comp_def, one_div, hkey] using h2

/-- Evaluation of the BCS gap integral. -/

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

lemma bcs_integral_eq {Δ ω : ℝ} (hΔ : 0 < Δ) :
    (∫ ξ in (0:ℝ)..ω, 1 / Real.sqrt (ξ ^ 2 + Δ ^ 2)) = Real.arsinh (ω / Δ) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => Real.arsinh (x / Δ))
    (f' := fun ξ : ℝ => 1 / Real.sqrt (ξ ^ 2 + Δ ^ 2))
    (fun x _ => hasDerivAt_arsinh_div hΔ x)
    ((continuous_bcs_kernel hΔ.ne').intervalIntegrable 0 ω)
  simpa using h

/-- **BCS gap equation.**  For any attractive coupling `g > 0` and cutoff `ω > 0`
there is a strictly positive gap `Δ` solving `g ∫₀^ω dξ / √(ξ² + Δ²) = 1`. -/

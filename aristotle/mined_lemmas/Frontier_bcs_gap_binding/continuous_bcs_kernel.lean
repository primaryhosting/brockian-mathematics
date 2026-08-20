import Mathlib
/-!
# Bcs Gap Binding
Category: Frontier Physics
Target: Frontier.bcs_gap_binding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Real intervalIntegral

/-- The BCS kernel `x ↦ 1 / √(x² + Δ²)` is continuous when `Δ ≠ 0`. -/

lemma continuous_bcs_kernel {Δ : ℝ} (hΔ : Δ ≠ 0) :
    Continuous fun x : ℝ => 1 / Real.sqrt (x ^ 2 + Δ ^ 2) := by
  have hpos : ∀ x : ℝ, Real.sqrt (x ^ 2 + Δ ^ 2) ≠ 0 := by
    intro x
    have : (0:ℝ) < x ^ 2 + Δ ^ 2 := by positivity
    exact ne_of_gt (Real.sqrt_pos.mpr this)
  exact continuous_const.div (by fun_prop) hpos

/-- The BCS gap integral: `∫₀^ω dx/√(x² + Δ²) = arsinh (ω/Δ)` for `Δ > 0`. -/

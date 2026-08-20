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

lemma integral_bcs_kernel {Δ : ℝ} (hΔ : 0 < Δ) (ω : ℝ) :
    (∫ x in (0:ℝ)..ω, 1 / Real.sqrt (x ^ 2 + Δ ^ 2)) = Real.arsinh (ω / Δ) := by
  have key : ∀ x ∈ Set.uIcc (0:ℝ) ω,
      HasDerivAt (fun t : ℝ => Real.arsinh (t / Δ)) (1 / Real.sqrt (x ^ 2 + Δ ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => t / Δ) (1 / Δ) x := by
      simpa [one_div] using (hasDerivAt_id x).div_const Δ
    have h2 := (Real.hasDerivAt_arsinh (x / Δ)).comp x h1
    have hs : Real.sqrt (1 + (x / Δ) ^ 2) = Real.sqrt (x ^ 2 + Δ ^ 2) / Δ := by
      rw [show (1:ℝ) + (x / Δ) ^ 2 = (x ^ 2 + Δ ^ 2) / Δ ^ 2 by field_simp; ring,
        Real.sqrt_div (by positivity), Real.sqrt_sq hΔ.le]
    have hsq : (0:ℝ) < Real.sqrt (x ^ 2 + Δ ^ 2) := Real.sqrt_pos.mpr (by positivity)
    convert h2 using 1
    rw [hs]
    field_simp
  have hint : IntervalIntegrable (fun x : ℝ => 1 / Real.sqrt (x ^ 2 + Δ ^ 2))
      MeasureTheory.volume 0 ω := (continuous_bcs_kernel hΔ.ne').intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt key hint]
  simp

/--
**BCS gap equation has a nonzero solution for any attractive coupling.**

For any attractive coupling strength `lam > 0` and any positive cutoff `ω > 0`, the BCS
gap equation
`lam * ∫₀^ω dξ / √(ξ² + Δ²) = 1`
has a strictly positive solution `Δ`, namely the standard BCS gap
`Δ = ω / sinh (1 / lam)`.  This is the Cooper-pairing/binding statement: an arbitrarily
weak attraction produces a nonzero gap.
-/

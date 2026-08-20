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
theorem bcs_gap_binding (lam ω : ℝ) (hlam : 0 < lam) (hω : 0 < ω) :
    ∃ Δ : ℝ, 0 < Δ ∧ Δ = ω / Real.sinh (1 / lam) ∧
      lam * (∫ x in (0:ℝ)..ω, 1 / Real.sqrt (x ^ 2 + Δ ^ 2)) = 1 := by
  have hs : 0 < Real.sinh (1 / lam) := by
    positivity
  refine ⟨ω / Real.sinh (1 / lam), by positivity, rfl, ?_⟩
  rw [integral_bcs_kernel (by positivity) ω]
  have : ω / (ω / Real.sinh (1 / lam)) = Real.sinh (1 / lam) := by
    field_simp
  rw [this, Real.arsinh_sinh]
  field_simp

end Frontier

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false


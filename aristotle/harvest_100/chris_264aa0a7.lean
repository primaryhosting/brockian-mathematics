/-
# Bcs Gap Binding
Category: Frontier Physics
Target: Frontier.bcs_gap_binding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

/-- The BCS pairing kernel `ξ ↦ 1 / √(ξ² + Δ²)`, integrated over the Debye shell
`[0, ω]`, evaluates to `arsinh (ω / Δ)`. -/
theorem integral_bcs_kernel (Δ ω : ℝ) (hΔ : 0 < Δ) :
    ∫ x in (0 : ℝ)..ω, 1 / Real.sqrt (x ^ 2 + Δ ^ 2) = Real.arsinh (ω / Δ) := by
  have key : ∀ x : ℝ, HasDerivAt (fun t : ℝ => Real.arsinh (t / Δ))
      (1 / Real.sqrt (x ^ 2 + Δ ^ 2)) x := by
    intro x
    have hbase : HasDerivAt (fun t : ℝ => t / Δ) (1 / Δ) x := by
      simpa [div_eq_mul_inv, one_div] using (hasDerivAt_id x).div_const Δ
    have h := hbase.arsinh
    have hsq : Real.sqrt (1 + (x / Δ) ^ 2) = Real.sqrt (x ^ 2 + Δ ^ 2) / Δ := by
      rw [eq_div_iff (ne_of_gt hΔ)]
      rw [show Δ = Real.sqrt (Δ ^ 2) by rw [Real.sqrt_sq hΔ.le]]
      rw [← Real.sqrt_mul (by positivity)]
      rw [Real.sqrt_sq hΔ.le]
      congr 1
      field_simp
      ring
    rw [hsq] at h
    have hpos : 0 < Real.sqrt (x ^ 2 + Δ ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have hval : ((Real.sqrt (x ^ 2 + Δ ^ 2) / Δ)⁻¹ • (1 / Δ) : ℝ)
        = 1 / Real.sqrt (x ^ 2 + Δ ^ 2) := by
      rw [smul_eq_mul]
      field_simp
    rwa [hval] at h
  have hcont : ContinuousOn (fun x : ℝ => 1 / Real.sqrt (x ^ 2 + Δ ^ 2))
      (Set.uIcc 0 ω) := by
    apply ContinuousOn.div continuousOn_const
      (Continuous.continuousOn (by fun_prop))
    intro x _
    exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => key x)
    (hcont.intervalIntegrable)]
  simp

/-- **Cooper pairing / BCS gap binding.**

For any attractive coupling `g > 0` and any positive Debye cutoff `ω`, the BCS gap
equation
`1 = g ∫₀^ω dξ / √(ξ² + Δ²)`
has a strictly positive solution `Δ`, namely the standard BCS gap
`Δ = ω / sinh (1 / g)`.  In particular a bound pair state exists for arbitrarily weak
attraction. -/
theorem bcs_gap_binding (g ω : ℝ) (hg : 0 < g) (hω : 0 < ω) :
    ∃ Δ : ℝ, 0 < Δ ∧ Δ = ω / Real.sinh (1 / g) ∧
      g * ∫ x in (0 : ℝ)..ω, 1 / Real.sqrt (x ^ 2 + Δ ^ 2) = 1 := by
  have hs : 0 < Real.sinh (1 / g) :=
    Mathlib.Meta.Positivity.sinh_pos_of_pos (by positivity)
  refine ⟨ω / Real.sinh (1 / g), by positivity, rfl, ?_⟩
  rw [integral_bcs_kernel _ _ (by positivity)]
  have hx : ω / (ω / Real.sinh (1 / g)) = Real.sinh (1 / g) := by
    field_simp
  rw [hx, Real.arsinh_sinh]
  field_simp

end Frontier


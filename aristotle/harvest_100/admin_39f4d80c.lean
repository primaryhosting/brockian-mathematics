/-
# Bcs Gap Binding
Category: Frontier Physics
Target: Frontier.bcs_gap_binding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bcs Gap Binding
Category: Frontier Physics
Target: Frontier.bcs_gap_binding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- The right-hand side of the (zero-temperature, constant density of states) BCS gap
equation: the pairing integral

  `∫_0^ω dξ / √(ξ² + Δ²)`

over the energy shell `[0, ω]` around the Fermi surface, for a gap parameter `Δ`. -/
noncomputable def bcsGapIntegral (Δ ω : ℝ) : ℝ := ∫ ξ in (0:ℝ)..ω, 1 / Real.sqrt (ξ ^ 2 + Δ ^ 2)

/-- Closed form of the BCS pairing integral for a positive gap: it equals `arsinh (ω / Δ)`. -/
theorem bcsGapIntegral_eq_arsinh (Δ ω : ℝ) (hΔ : 0 < Δ) :
    bcsGapIntegral Δ ω = Real.arsinh (ω / Δ) := by
  have hderiv : ∀ ξ ∈ Set.uIcc (0:ℝ) ω,
      HasDerivAt (fun t : ℝ => Real.arsinh (t / Δ)) (1 / Real.sqrt (ξ ^ 2 + Δ ^ 2)) ξ := by
    intro ξ _
    have h1 : HasDerivAt (fun t : ℝ => t / Δ) (1 / Δ) ξ := by
      simpa using (hasDerivAt_id ξ).div_const Δ
    have h2 := (Real.hasDerivAt_arsinh (ξ / Δ)).comp ξ h1
    rw [one_div]
    convert h2 using 1
    have key : (1 + (ξ / Δ) ^ 2) * Δ ^ 2 = ξ ^ 2 + Δ ^ 2 := by field_simp; ring
    have hs : Real.sqrt (ξ ^ 2 + Δ ^ 2) = Real.sqrt (1 + (ξ / Δ) ^ 2) * Δ := by
      rw [← key, Real.sqrt_mul (by positivity), Real.sqrt_sq hΔ.le]
    have hp : (0:ℝ) < Real.sqrt (1 + (ξ / Δ) ^ 2) := Real.sqrt_pos.2 (by positivity)
    rw [hs]; field_simp
  have hint : IntervalIntegrable (fun ξ : ℝ => 1 / Real.sqrt (ξ ^ 2 + Δ ^ 2))
      MeasureTheory.volume 0 ω := by
    apply Continuous.intervalIntegrable
    apply Continuous.div continuous_const
    · exact Real.continuous_sqrt.comp (by continuity)
    · intro ξ; exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
  rw [bcsGapIntegral, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-- **Cooper pairing / BCS gap binding.**

For any attractive coupling strength `g > 0` and any positive Debye cutoff `ω`, the BCS gap
equation

  `g * ∫_0^ω dξ / √(ξ² + Δ²) = 1`

admits a *nonzero* (indeed strictly positive) solution `Δ`, given explicitly by the familiar
BCS form `Δ = ω / sinh (1 / g)`.  Thus an arbitrarily weak attraction always binds a gap. -/
theorem bcs_gap_binding (g ω : ℝ) (hg : 0 < g) (hω : 0 < ω) :
    ∃ Δ : ℝ, Δ ≠ 0 ∧ 0 < Δ ∧ g * bcsGapIntegral Δ ω = 1 := by
  have hsinh : 0 < Real.sinh (1 / g) := Real.sinh_pos_iff.2 (by positivity)
  refine ⟨ω / Real.sinh (1 / g), by positivity, by positivity, ?_⟩
  rw [bcsGapIntegral_eq_arsinh _ _ (by positivity)]
  have : ω / (ω / Real.sinh (1 / g)) = Real.sinh (1 / g) := by
    field_simp
  rw [this, Real.arsinh_sinh]
  field_simp

end Frontier


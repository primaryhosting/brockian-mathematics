import Mathlib
/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Frontier

/-- The Berry flux of a band: the integral of the Berry curvature `F` over the
Brillouin torus `[0, 2π] × [0, 2π]`. -/
noncomputable def berryFlux (F : ℝ → ℝ → ℝ) : ℝ :=
  ∫ k₁ in (0:ℝ)..(2 * Real.pi), ∫ k₂ in (0:ℝ)..(2 * Real.pi), F k₁ k₂

/-- The Chern number of a band, i.e. the Berry flux in units of `2π`. -/
noncomputable def chernNumber (F : ℝ → ℝ → ℝ) : ℝ := berryFlux F / (2 * Real.pi)

/-- The Hall conductance predicted by the TKNN formula: the Chern number times the
conductance quantum `e² / h`. -/
noncomputable def hallConductance (e hPlanck : ℝ) (F : ℝ → ℝ → ℝ) : ℝ :=
  chernNumber F * (e ^ 2 / hPlanck)

/-- Quantization of the Chern number: a Berry flux of `2π n` gives Chern number `n`. -/
theorem chernNumber_of_berryFlux {F : ℝ → ℝ → ℝ} {n : ℤ}
    (hF : berryFlux F = 2 * Real.pi * n) : chernNumber F = (n : ℝ) := by
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  rw [chernNumber, hF, mul_div_assoc]
  field_simp

/-- The Berry curvature of the model band used as the base case: a smooth,
`2π`-periodic curvature on the Brillouin torus carrying one flux quantum. -/
noncomputable def modelCurvature : ℝ → ℝ → ℝ :=
  fun k₁ k₂ => (1 + Real.cos k₁ * Real.cos k₂) / (2 * Real.pi)

/-- The model band carries exactly one flux quantum. -/
theorem berryFlux_modelCurvature : berryFlux modelCurvature = 2 * Real.pi := by
  have inner : ∀ k₁ : ℝ,
      (∫ k₂ in (0:ℝ)..(2 * Real.pi), modelCurvature k₁ k₂) = 1 := by
    intro k₁
    simp only [modelCurvature]
    rw [intervalIntegral.integral_div,
      intervalIntegral.integral_add intervalIntegrable_const
        (intervalIntegral.intervalIntegrable_cos.const_mul _),
      intervalIntegral.integral_const_mul, integral_cos]
    simp [Real.sin_two_pi]
  rw [berryFlux]
  simp [inner]

/-- The model band has Chern number one. -/
theorem chernNumber_modelCurvature : chernNumber modelCurvature = 1 := by
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  rw [chernNumber, berryFlux_modelCurvature, div_self hpi]

/--
**TKNN (Thouless–Kohmoto–Nightingale–den Nijs).**

For a filled band whose Berry flux over the Brillouin torus is the quantized value
`2π n` (`n : ℤ` the Chern number), the Hall conductance is exactly `n · e²/h`;
it vanishes precisely when the Chern number vanishes (for a nonzero charge and
Planck constant), and the explicit model band `modelCurvature`, which carries one
flux quantum, realizes the base case `σ_xy = e²/h`.
-/
theorem tknn_chern_hall (e hPlanck : ℝ) (he : e ≠ 0) (hh : hPlanck ≠ 0)
    (F : ℝ → ℝ → ℝ) (n : ℤ) (hF : berryFlux F = 2 * Real.pi * n) :
    hallConductance e hPlanck F = (n : ℝ) * (e ^ 2 / hPlanck) ∧
      (hallConductance e hPlanck F = 0 ↔ n = 0) ∧
      hallConductance e hPlanck modelCurvature = e ^ 2 / hPlanck := by
  have hq : e ^ 2 / hPlanck ≠ 0 := div_ne_zero (pow_ne_zero 2 he) hh
  have hmain : hallConductance e hPlanck F = (n : ℝ) * (e ^ 2 / hPlanck) := by
    rw [hallConductance, chernNumber_of_berryFlux hF]
  refine ⟨hmain, ?_, ?_⟩
  · rw [hmain]
    constructor
    · intro h
      rcases mul_eq_zero.1 h with h0 | h0
      · exact_mod_cast h0
      · exact absurd h0 hq
    · rintro rfl
      simp
  · rw [hallConductance, chernNumber_modelCurvature, one_mul]

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


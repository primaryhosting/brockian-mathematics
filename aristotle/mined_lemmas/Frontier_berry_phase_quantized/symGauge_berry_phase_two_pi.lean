/-
# Berry Phase Quantized
Category: Frontier Physics
Target: Frontier.berry_phase_quantized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

open Set MeasureTheory

namespace Frontier

/-- The **Berry connection** is modelled as a real one-form on a two-dimensional parameter
space, i.e. a map `A : ℝ × ℝ → ℝ × ℝ` whose value `A p = (A₁ p, A₂ p)` gives the components
of the form `A₁ dx + A₂ dy` at the parameter point `p`. -/
abbrev BerryConnection := ℝ × ℝ → ℝ × ℝ

/-- The **Berry curvature** of a Berry connection `A` at a parameter point `p`:
`F = ∂₁ A₂ - ∂₂ A₁`, the exterior derivative of the connection one-form. -/

theorem symGauge_berry_phase_two_pi :
    berryFlux (symGauge (2 * Real.pi)) 0 0 1 1 = 2 * Real.pi ∧
      berryPhase (symGauge (2 * Real.pi)) 0 0 1 1 = 2 * Real.pi := by
  have hflux : berryFlux (symGauge (2 * Real.pi)) 0 0 1 1 = 2 * Real.pi := by
    simp [berryFlux, symGauge_curvature]
  refine ⟨hflux, ?_⟩
  have hint : IntegrableOn (berryCurvature (symGauge (2 * Real.pi)))
      (uIcc (0 : ℝ) 1 ×ˢ uIcc (0 : ℝ) 1) := by
    have hconst : IntegrableOn (fun _ : ℝ × ℝ => 2 * Real.pi)
        (uIcc (0 : ℝ) 1 ×ˢ uIcc (0 : ℝ) 1) := by
      refine MeasureTheory.integrableOn_const (C := 2 * Real.pi) ?_ ?_
      · rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
        simp [Real.volume_Icc, uIcc_of_le]
      · simp [enorm_mul, ENNReal.mul_eq_top]
    exact hconst.congr_fun (fun p _ => (symGauge_curvature _ p).symm)
      (measurableSet_uIcc.prod measurableSet_uIcc)
  have h := berry_phase_quantized (symGauge (2 * Real.pi)) 0 0 1 1 1
    (symGauge_differentiable_fst _) (symGauge_differentiable_snd _) hint
    (by rw [hflux]; push_cast; ring)
  simpa using h

/-- **Quantization, subgroup form.**  If the Berry flux lies in the subgroup `2π ℤ` of `ℝ`,
then so does the Berry phase around the closed boundary loop. -/

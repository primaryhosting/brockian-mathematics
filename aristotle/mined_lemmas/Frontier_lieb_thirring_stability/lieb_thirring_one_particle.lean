/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

open MeasureTheory

/-! ## The pointwise (Young) inequality underlying stability -/

/-- The Lieb–Thirring stability constant appearing in the bound
`Kc * a ^ (5/3) - t * a ≥ - ltConst Kc * t ^ (5/2)`. -/

theorem lieb_thirring_one_particle (ψ : Space → ℂ) (h1 : ContDiff ℝ 1 ψ)
    (hcs : HasCompactSupport ψ) (hnorm : (∫ x, ‖ψ x‖ ^ 2) = 1) :
    (∫ x, (density (fun _ : Fin 1 => ψ) x) ^ (5 / 3 : ℝ)) ≤ sobolevConst ^ 2 * kineticEnergy ψ := by
  have hcd : Continuous (fderiv ℝ ψ) := h1.continuous_fderiv (by norm_num)
  have hfds : HasCompactSupport (fderiv ℝ ψ) := hcs.fderiv (𝕜 := ℝ)
  -- densities
  have hdens : ∀ x, (density (fun _ : Fin 1 => ψ) x) ^ (5 / 3 : ℝ) = ‖ψ x‖ ^ (10 / 3 : ℝ) := by
    intro x
    have hn : (0 : ℝ) ≤ ‖ψ x‖ := norm_nonneg _
    simp only [density, Finset.univ_unique, Finset.sum_singleton]
    rw [← Real.rpow_natCast (‖ψ x‖) 2, ← Real.rpow_mul hn]
    norm_num
  -- kinetic energy dominates the operator-norm integral
  have hgc : Continuous (gradSqNorm ψ) := by
    refine continuous_finset_sum _ fun j _ => ?_
    exact ((hcd.clm_apply continuous_const).norm).pow 2
  have hgs : HasCompactSupport (gradSqNorm ψ) := by
    apply HasCompactSupport.comp_left
      (g := fun L : Space →L[ℝ] ℂ => ∑ j : Fin 3, ‖L (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) hfds
    simp
  have hopc : Continuous (fun x => ‖fderiv ℝ ψ x‖ ^ 2) := (hcd.norm).pow 2
  have hops : HasCompactSupport (fun x => ‖fderiv ℝ ψ x‖ ^ 2) := by
    apply HasCompactSupport.comp_left (g := fun L : Space →L[ℝ] ℂ => ‖L‖ ^ 2) hfds
    simp
  have hTle : (∫ x, ‖fderiv ℝ ψ x‖ ^ 2) ≤ kineticEnergy ψ :=
    integral_mono (hopc.integrable_of_hasCompactSupport hops)
      (hgc.integrable_of_hasCompactSupport hgs) (opNorm_sq_le_gradSqNorm ψ)
  -- Sobolev + Hölder
  set B : ℝ := ∫ x, ‖ψ x‖ ^ 6 with hB
  set T : ℝ := ∫ x, ‖fderiv ℝ ψ x‖ ^ 2 with hT
  have hB0 : 0 ≤ B := integral_nonneg fun x => by positivity
  have hT0 : 0 ≤ T := integral_nonneg fun x => by positivity
  have hsob := sobolev_six_le ψ h1 hcs
  have hsq : B ^ (1 / 3 : ℝ) ≤ sobolevConst ^ 2 * T := by
    have h6 : (0 : ℝ) ≤ B ^ (1 / 6 : ℝ) := Real.rpow_nonneg hB0 _
    have hmul := mul_self_le_mul_self h6 hsob
    have e1 : B ^ (1 / 6 : ℝ) * B ^ (1 / 6 : ℝ) = B ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_add' hB0 (by norm_num)]
      norm_num
    have e2 : (sobolevConst * T ^ (1 / 2 : ℝ)) * (sobolevConst * T ^ (1 / 2 : ℝ))
        = sobolevConst ^ 2 * T := by
      have : T ^ (1 / 2 : ℝ) * T ^ (1 / 2 : ℝ) = T := by
        rw [← Real.rpow_add' hT0 (by norm_num)]
        norm_num
      nlinarith [this]
    rwa [e1, e2] at hmul
  have hhol := holder_interp_ten_thirds ψ h1.continuous hcs
  rw [hnorm] at hhol
  simp only [Real.one_rpow, one_mul] at hhol
  simp only [hdens]
  calc (∫ x, ‖ψ x‖ ^ (10 / 3 : ℝ)) ≤ B ^ (1 / 3 : ℝ) := hhol
    _ ≤ sobolevConst ^ 2 * T := hsq
    _ ≤ sobolevConst ^ 2 * kineticEnergy ψ := by
        have : (0 : ℝ) ≤ sobolevConst ^ 2 := by positivity
        nlinarith [hTle]


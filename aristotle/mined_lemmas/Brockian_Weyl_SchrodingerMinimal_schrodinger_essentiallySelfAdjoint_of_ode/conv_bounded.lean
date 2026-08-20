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

/-
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Complex
open scoped Convolution

namespace Brockian.Weyl.SchrodingerMinimal

/-! ## Test functions and the minimal Schrödinger expression -/

/-- A test function on the line: smooth with compact support. -/

private theorem conv_bounded {u ρ : ℝ → ℂ} (hu : MemLp u 2 volume) (hρc : Continuous ρ)
    (hcρ : HasCompactSupport ρ) (t : ℝ) :
    ‖∫ x, (starRingEnd ℂ) (u x) * ρ (t - x)‖
      ≤ (∫ x, ‖u x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) * (∫ x, ‖ρ x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
  have hρt : MemLp (fun x => ρ (t - x)) (ENNReal.ofReal 2) volume := by
    apply Continuous.memLp_of_hasCompactSupport
    · exact hρc.comp (continuous_const.sub continuous_id)
    · exact hcρ.comp_homeomorph (Homeomorph.subLeft t)
  have hu2 : MemLp (fun x => (starRingEnd ℂ) (u x)) (ENNReal.ofReal 2) volume := by
    have hu' : MemLp u (ENNReal.ofReal 2) volume := by simpa using hu
    refine ⟨Complex.continuous_conj.comp_aestronglyMeasurable hu'.1, ?_⟩
    have : eLpNorm (fun x => (starRingEnd ℂ) (u x)) (ENNReal.ofReal 2) volume
        = eLpNorm u (ENNReal.ofReal 2) volume := by
      apply eLpNorm_congr_norm_ae
      filter_upwards with x
      simp
    rw [this]
    exact hu'.2
  calc ‖∫ x, (starRingEnd ℂ) (u x) * ρ (t - x)‖
      ≤ ∫ x, ‖(starRingEnd ℂ) (u x) * ρ (t - x)‖ := norm_integral_le_integral_norm _
    _ = ∫ x, ‖(starRingEnd ℂ) (u x)‖ * ‖ρ (t - x)‖ := by simp
    _ ≤ (∫ x, ‖(starRingEnd ℂ) (u x)‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
          * (∫ x, ‖ρ (t - x)‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
        integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hu2 hρt
    _ = _ := by
        congr 1
        · simp
        · congr 1
          exact integral_sub_left_eq_self (fun x => ‖ρ x‖ ^ (2 : ℝ)) volume t

/-! ## Symmetry of the minimal operator -/

/-- The minimal Schrödinger operator is symmetric on test functions. -/

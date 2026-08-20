/-
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Metric Set Complex

namespace Math

noncomputable section

/-! ## Step 1: the radial projection onto the closed unit disk of `ℂ`. -/

/-- Radial projection of `ℂ` onto the closed unit disk. -/

theorem exists_retraction_of_no_fixed_point (f : ℂ → ℂ)
    (hf : ContinuousOn f (closedBall 0 1)) (hmaps : MapsTo f (closedBall 0 1) (closedBall 0 1))
    (hnofix : ∀ x ∈ closedBall (0 : ℂ) 1, f x ≠ x) :
    ∃ g : ℂ → ℂ, Continuous g ∧ (∀ z, ‖g z‖ = 1) ∧ (∀ z, ‖z‖ = 1 → g z = z) := by
  have hmemy : ∀ z : ℂ, proj z ∈ closedBall (0:ℂ) 1 := fun z =>
    mem_closedBall_zero_iff.mpr (norm_proj_le z)
  set P : ℂ → ℂ := fun z => proj z
  set Q : ℂ → ℂ := fun z => f (proj z)
  have hQcont : Continuous Q := hf.comp_continuous continuous_proj hmemy
  have hQnorm : ∀ z, ‖Q z‖ ≤ 1 := fun z => mem_closedBall_zero_iff.mp (hmaps (hmemy z))
  set d : ℂ → ℂ := fun z => P z - Q z
  have hdeq : ∀ z, d z = P z - Q z := fun z => rfl
  have hdne : ∀ z, d z ≠ 0 := by
    intro z hz
    refine hnofix (proj z) (hmemy z) ?_
    have : P z = Q z := by rw [hdeq] at hz; rwa [sub_eq_zero] at hz
    exact this.symm
  have hdnorm : ∀ z, ‖d z‖ ≠ 0 := fun z => norm_ne_zero_iff.mpr (hdne z)
  -- the unit vector pointing from `f z` to `z`
  set u : ℂ → ℂ := fun z => ‖d z‖⁻¹ • d z
  have hueq : ∀ z, u z = ‖d z‖⁻¹ • d z := fun z => rfl
  have hunorm : ∀ z, ‖u z‖ = 1 := by
    intro z
    rw [hueq z, norm_smul]
    simp only [norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact inv_mul_cancel₀ (hdnorm z)
  set A : ℂ → ℝ := fun z => inner ℝ (P z) (u z)
  have hAeq : ∀ z, A z = inner ℝ (P z) (u z) := fun z => rfl
  -- the distance one has to travel from `z` in direction `u z` to reach the unit circle
  set T : ℂ → ℝ := fun z => -A z + Real.sqrt ((A z)^2 + 1 - ‖P z‖^2)
  have hTeq : ∀ z, T z = -A z + Real.sqrt ((A z)^2 + 1 - ‖P z‖^2) := fun z => rfl
  refine ⟨fun z => P z + T z • u z, ?_, ?_, ?_⟩
  · have hPc : Continuous P := continuous_proj
    have hdc : Continuous d := hPc.sub hQcont
    have huc : Continuous u := Continuous.smul ((hdc.norm).inv₀ hdnorm) hdc
    have hAc : Continuous A := hPc.inner huc
    have hTc : Continuous T :=
      Continuous.add hAc.neg (((hAc.pow 2).add continuous_const).sub (hPc.norm.pow 2)).sqrt
    exact hPc.add (hTc.smul huc)
  · intro z
    have hD : 0 ≤ (A z)^2 + 1 - ‖P z‖^2 := by
      have := norm_proj_le z
      nlinarith [sq_nonneg (A z), norm_nonneg (P z)]
    have hS : (Real.sqrt ((A z)^2 + 1 - ‖P z‖^2))^2 = (A z)^2 + 1 - ‖P z‖^2 := Real.sq_sqrt hD
    have hsq : ‖P z + T z • u z‖^2 = 1 := by
      rw [norm_add_sq_real, real_inner_smul_right, norm_smul]
      simp only [Real.norm_eq_abs, sq_abs, hunorm z, mul_one, ← hAeq z]
      rw [hTeq z]
      nlinarith [hS]
    show ‖P z + T z • u z‖ = 1
    nlinarith [norm_nonneg (P z + T z • u z), hsq]
  · intro z hz
    have hPz : P z = z := proj_eq_self (le_of_eq hz)
    have hAnn : 0 ≤ A z := by
      have h1 : (inner ℝ z (Q z) : ℝ) ≤ 1 := by
        have := real_inner_le_norm z (Q z)
        have h2 := hQnorm z
        nlinarith [norm_nonneg (Q z)]
      have hAz : A z = ‖d z‖⁻¹ * (‖z‖^2 - inner ℝ z (Q z)) := by
        rw [hAeq z, hueq z, real_inner_smul_right, hdeq z, inner_sub_right,
          real_inner_self_eq_norm_sq, hPz]
      rw [hAz, hz]
      have hpos : (0:ℝ) < ‖d z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm (hdnorm z))
      have hinv : 0 < ‖d z‖⁻¹ := by positivity
      nlinarith
    have hTz : T z = 0 := by
      rw [hTeq z, hPz, hz]
      have h3 : (A z)^2 + 1 - 1^2 = (A z)^2 := by ring
      rw [h3, Real.sqrt_sq hAnn]
      ring
    show P z + T z • u z = z
    rw [hTz, hPz]
    simp

/-- **Brouwer's fixed point theorem** in the complex plane. -/

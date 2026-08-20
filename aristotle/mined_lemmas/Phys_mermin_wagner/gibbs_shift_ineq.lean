/-
The classical XY model on a finite graph, and the finite-volume Mermin-Wagner bound
on its magnetization in terms of the Dirichlet energy of a spin-wave profile.
-/
import RequestProject.Core

open MeasureTheory Real

namespace Phys

noncomputable section

variable {S ι : Type} [Fintype S]

/-- The energy of the classical XY model on a finite graph whose edges are indexed by
`bonds`, with endpoints `src` and `tgt`, coupling `J` and external field `h`. -/

lemma gibbs_shift_ineq {H A : Cfg S → ℝ} (hH : Continuous H) (hA : Continuous A)
    (hA0 : ∀ θ, 0 ≤ A θ) {β K : ℝ} (hβ : 0 ≤ β) (w : Cfg S)
    (hK : ∀ θ, H (θ + w) + H (θ - w) ≤ 2 * H θ + K) :
    2 * Real.exp (-(β * K) / 2) * gibbsAvg H β A
      ≤ gibbsAvg H β (fun θ => A (θ + w)) + gibbsAvg H β (fun θ => A (θ - w)) := by
  have hZ := gibbsZ_pos hH β
  have hAw : Continuous fun θ : Cfg S => A (θ + w) := hA.comp (continuous_id.add continuous_const)
  have hAw' : Continuous fun θ : Cfg S => A (θ - w) := hA.comp (continuous_id.sub continuous_const)
  -- rewrite the two shifted numerators using translation invariance
  have key1 : ∫ θ, A (θ + w) * Real.exp (-β * H θ)
      = ∫ θ, A θ * Real.exp (-β * H (θ - w)) := by
    have := integral_add_right_eq_self
      (μ := (volume : Measure (Cfg S))) (fun θ => A θ * Real.exp (-β * H (θ - w))) w
    simpa using this
  have key2 : ∫ θ, A (θ - w) * Real.exp (-β * H θ)
      = ∫ θ, A θ * Real.exp (-β * H (θ + w)) := by
    have := integral_add_right_eq_self
      (μ := (volume : Measure (Cfg S))) (fun θ => A θ * Real.exp (-β * H (θ + w))) (-w)
    simpa [sub_eq_add_neg] using this
  -- the pointwise bound
  have hpt : ∀ θ : Cfg S,
      2 * Real.exp (-(β * K) / 2) * (A θ * Real.exp (-β * H θ))
        ≤ A θ * Real.exp (-β * H (θ - w)) + A θ * Real.exp (-β * H (θ + w)) := by
    intro θ
    have hmid := two_exp_mid_le (-β * H (θ - w)) (-β * H (θ + w))
    have hle : -(β * K) / 2 + -β * H θ ≤ (-β * H (θ - w) + -β * H (θ + w)) / 2 := by
      have := hK θ
      nlinarith [hK θ, hβ]
    have hexp : Real.exp (-(β * K) / 2) * Real.exp (-β * H θ)
        ≤ Real.exp ((-β * H (θ - w) + -β * H (θ + w)) / 2) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hle
    have h2 : 2 * (Real.exp (-(β * K) / 2) * Real.exp (-β * H θ))
        ≤ Real.exp (-β * H (θ - w)) + Real.exp (-β * H (θ + w)) := by
      linarith [hmid, hexp]
    have := mul_le_mul_of_nonneg_left h2 (hA0 θ)
    nlinarith [this, hA0 θ]
  -- integrate
  have hint : 2 * Real.exp (-(β * K) / 2) * (∫ θ, A θ * Real.exp (-β * H θ))
      ≤ (∫ θ, A θ * Real.exp (-β * H (θ - w))) + ∫ θ, A θ * Real.exp (-β * H (θ + w)) := by
    have hi1 : Integrable (fun θ : Cfg S => A θ * Real.exp (-β * H (θ - w)))
        (volume : Measure (Cfg S)) :=
      integrable_of_continuous (hA.mul (Real.continuous_exp.comp (continuous_const.mul
        (hH.comp (continuous_id.sub continuous_const)))))
    have hi2 : Integrable (fun θ : Cfg S => A θ * Real.exp (-β * H (θ + w)))
        (volume : Measure (Cfg S)) :=
      integrable_of_continuous (hA.mul (Real.continuous_exp.comp (continuous_const.mul
        (hH.comp (continuous_id.add continuous_const)))))
    have hmono := integral_mono ((integrable_obs hH hA β).const_mul _) (hi1.add hi2) hpt
    simp only [Pi.add_apply] at hmono
    rw [integral_const_mul, integral_add hi1 hi2] at hmono
    exact hmono
  unfold gibbsAvg
  rw [key1, key2, ← add_div]
  calc 2 * Real.exp (-(β * K) / 2) * ((∫ θ, A θ * Real.exp (-β * H θ)) / gibbsZ H β)
      = (2 * Real.exp (-(β * K) / 2) * ∫ θ, A θ * Real.exp (-β * H θ)) / gibbsZ H β := by ring
    _ ≤ ((∫ θ, A θ * Real.exp (-β * H (θ - w))) + ∫ θ, A θ * Real.exp (-β * H (θ + w)))
          / gibbsZ H β := by gcongr

/-- The Gibbs average of an observable bounded by `1` is bounded by `1`: `gibbsAvg` really is
an average with respect to a probability measure. -/

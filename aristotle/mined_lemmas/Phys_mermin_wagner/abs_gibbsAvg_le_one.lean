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

lemma abs_gibbsAvg_le_one {H A : Cfg S → ℝ} (hH : Continuous H) (hA : Continuous A) (β : ℝ)
    (hbound : ∀ θ, |A θ| ≤ 1) : |gibbsAvg H β A| ≤ 1 := by
  have hZ := gibbsZ_pos hH β
  have hfc : Continuous fun θ : Cfg S => Real.exp (-β * H θ) :=
    Real.continuous_exp.comp (continuous_const.mul hH)
  have h1 : |∫ θ, A θ * Real.exp (-β * H θ)| ≤ ∫ θ, |A θ * Real.exp (-β * H θ)| :=
    abs_integral_le_integral_abs
  have h2 : ∫ θ, |A θ * Real.exp (-β * H θ)| ≤ gibbsZ H β := by
    refine integral_mono ((integrable_obs hH hA β).abs) (integrable_of_continuous hfc) ?_
    intro θ
    simp only
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (hbound θ)
  unfold gibbsAvg
  rw [abs_div, abs_of_pos hZ, div_le_one hZ]
  linarith


end Gibbs

end

end Phys

/-
The harmonic spin-wave profile: it equals `1` at the centre, vanishes outside a ball of
radius `R`, and has Dirichlet energy `O(1 / log R)` in dimension `d ≤ 2`.
-/
import RequestProject.Lattice

open MeasureTheory Real Filter

namespace Phys

noncomputable section

/-- The harmonic sum `∑_{s=1}^{R} 1/s`. -/

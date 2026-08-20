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

lemma gibbsZ_pos {H : Cfg S → ℝ} (hH : Continuous H) (β : ℝ) : 0 < gibbsZ H β := by
  have hfc : Continuous fun θ : Cfg S => Real.exp (-β * H θ) :=
    Real.continuous_exp.comp (continuous_const.mul hH)
  obtain ⟨θ₀, -, hθ₀'⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty) hfc.continuousOn
  have hθ₀ : ∀ y : Cfg S, Real.exp (-β * H θ₀) ≤ Real.exp (-β * H y) :=
    fun y => hθ₀' (Set.mem_univ y)
  have hvol : 0 < ((volume : Measure (Cfg S)) Set.univ).toReal :=
    ENNReal.toReal_pos (ne_of_gt volume_univ_pos) (measure_ne_top _ _)
  have hmono : ∫ _ : Cfg S, Real.exp (-β * H θ₀) ≤ ∫ θ, Real.exp (-β * H θ) :=
    integral_mono (integrable_const _) (integrable_of_continuous hfc) hθ₀
  have hconst : ∫ _ : Cfg S, Real.exp (-β * H θ₀)
      = ((volume : Measure (Cfg S)) Set.univ).toReal * Real.exp (-β * H θ₀) := by
    simp [integral_const, smul_eq_mul, measureReal_def]
  have : 0 < ((volume : Measure (Cfg S)) Set.univ).toReal * Real.exp (-β * H θ₀) := by
    have := Real.exp_pos (-β * H θ₀); positivity
  unfold gibbsZ
  linarith [hmono, hconst ▸ hmono]


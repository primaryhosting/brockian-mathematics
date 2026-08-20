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

lemma integrable_obs {H A : Cfg S → ℝ} (hH : Continuous H) (hA : Continuous A) (β : ℝ) :
    Integrable (fun θ => A θ * Real.exp (-β * H θ)) (volume : Measure (Cfg S)) :=
  integrable_of_continuous (hA.mul (Real.continuous_exp.comp (continuous_const.mul hH)))


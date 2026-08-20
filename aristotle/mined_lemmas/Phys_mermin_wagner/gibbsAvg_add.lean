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

lemma gibbsAvg_add {H A B : Cfg S → ℝ} (hH : Continuous H) (hA : Continuous A)
    (hB : Continuous B) (β : ℝ) :
    gibbsAvg H β (fun θ => A θ + B θ) = gibbsAvg H β A + gibbsAvg H β B := by
  unfold gibbsAvg
  rw [← add_div]
  congr 1
  rw [← integral_add (integrable_obs hH hA β) (integrable_obs hH hB β)]
  congr 1 with θ
  ring


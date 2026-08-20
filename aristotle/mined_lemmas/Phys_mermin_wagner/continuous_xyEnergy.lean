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

lemma continuous_xyEnergy (bonds : Finset ι) (src tgt : ι → S) (J h : ℝ) :
    Continuous (xyEnergy bonds src tgt J h) := by
  unfold xyEnergy
  refine Continuous.sub (continuous_const.mul (continuous_finset_sum _ fun b _ => ?_))
    (continuous_const.mul (continuous_finset_sum _ fun x _ => ?_))
  · exact continuous_cosC.comp ((continuous_apply _).sub (continuous_apply _))
  · exact continuous_cosC.comp (continuous_apply _)

/-- The magnetization at the site `o`: the Gibbs expectation of `cos` of the spin there. -/

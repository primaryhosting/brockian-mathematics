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

lemma gibbsAvg_const {H : Cfg S → ℝ} (hH : Continuous H) (β c : ℝ) :
    gibbsAvg H β (fun _ => c) = c := by
  have hZ := gibbsZ_pos hH β
  unfold gibbsAvg
  have hz : (∫ θ : Cfg S, Real.exp (-β * H θ)) = gibbsZ H β := rfl
  rw [integral_const_mul, hz, mul_div_assoc, div_self (ne_of_gt hZ), mul_one]


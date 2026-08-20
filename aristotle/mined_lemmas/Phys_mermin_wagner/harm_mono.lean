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

lemma harm_mono : Monotone harm := by
  intro a b hab
  unfold harm
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) ?_
  intro i _ _
  positivity


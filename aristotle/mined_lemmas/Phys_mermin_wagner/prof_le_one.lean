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

lemma prof_le_one (R m : ℕ) : prof R m ≤ 1 := by
  unfold prof
  refine max_le zero_le_one ?_
  have : 0 ≤ harm m / harm R := div_nonneg (harm_nonneg m) (harm_nonneg R)
  linarith


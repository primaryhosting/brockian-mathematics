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

lemma one_le_harm {R : ℕ} (hR : 1 ≤ R) : 1 ≤ harm R := by
  have h1 : harm 1 = 1 := by norm_num [harm]
  calc (1 : ℝ) = harm 1 := h1.symm
    _ ≤ harm R := harm_mono hR


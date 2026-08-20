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

lemma prof_eq_zero_of_le {R m : ℕ} (hR : 1 ≤ R) (h : R ≤ m) : prof R m = 0 := by
  unfold prof
  have h1 : harm R ≤ harm m := harm_mono h
  have h2 : 1 ≤ harm m / harm R := (one_le_div (harm_pos hR)).mpr h1
  exact max_eq_left (by linarith)


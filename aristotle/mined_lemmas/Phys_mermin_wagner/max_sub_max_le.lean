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

lemma max_sub_max_le {u v : ℝ} (h : v ≤ u) : max 0 u - max 0 v ≤ u - v := by
  rcases le_or_gt u 0 with hu | hu
  · have hv : v ≤ 0 := le_trans h hu
    rw [max_eq_left hu, max_eq_left hv]
    linarith
  · rcases le_or_gt v 0 with hv | hv
    · rw [max_eq_left hv, max_eq_right hu.le]
      linarith
    · rw [max_eq_right hv.le, max_eq_right hu.le]


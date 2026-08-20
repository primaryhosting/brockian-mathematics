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

lemma prof_antitone {R : ℕ} : Antitone (prof R) := by
  intro a b hab
  unfold prof
  refine max_le_max le_rfl ?_
  have : harm a ≤ harm b := harm_mono hab
  have hR := harm_nonneg R
  rcases eq_or_lt_of_le hR with h | h
  · simp [← h]
  · apply sub_le_sub_left
    gcongr

/-- One-step decay of the profile. -/

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

lemma swProfile_center (d L R : ℕ) : swProfile d L R (center d L) = Real.pi := by
  unfold swProfile
  rw [rad_center, prof_zero, mul_one]

/-! ### Geometry of a bond -/


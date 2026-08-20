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

lemma abs_cosC_le_one (z : Circ) : |cosC z| ≤ 1 := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (2 * Real.pi)) z
  simpa using Real.abs_cos_le_one a

/-- The elementary trigonometric inequality behind the spin–wave estimate:
shifting a spin by `± s` costs at most `s ^ 2` in second difference. -/

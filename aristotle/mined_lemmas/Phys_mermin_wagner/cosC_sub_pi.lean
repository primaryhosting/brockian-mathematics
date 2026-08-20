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

lemma cosC_sub_pi (z : Circ) : cosC (z - ((Real.pi : ℝ) : Circ)) = -cosC z := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (2 * Real.pi)) z
  have h1 : ((a : ℝ) : Circ) - ((Real.pi : ℝ) : Circ) = ((a - Real.pi : ℝ) : Circ) := rfl
  show cosC (((a : ℝ) : Circ) - _) = -cosC ((a : ℝ) : Circ)
  rw [h1, cosC_coe, cosC_coe, Real.cos_sub_pi]

section Gibbs

variable {S : Type} [Fintype S]


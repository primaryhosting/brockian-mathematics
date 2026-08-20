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

lemma spinWave_apply (v : S → ℝ) (x : S) : spinWave v x = ((v x : ℝ) : Circ) := rfl

/-- Second-difference bound for the XY energy under a spin-wave shift: the cost is at most
the Dirichlet energy of the profile plus the field term. -/

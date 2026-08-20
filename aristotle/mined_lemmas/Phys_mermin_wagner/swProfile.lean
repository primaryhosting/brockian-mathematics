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

def swProfile (d L R : ℕ) : Site d L → ℝ := fun x => Real.pi * prof R (rad x)

/-- The magnetization at the centre of the box `{0,…,2L}^d` for the classical XY model
with inverse temperature `β`, coupling `J` and external field `h`. -/

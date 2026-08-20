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

def bondSet (d L : ℕ) : Finset (Site d L × Fin d) :=
  Finset.univ.filter fun p => (p.1 p.2 : ℕ) + 1 ≤ 2 * L

/-- The first endpoint of a bond. -/

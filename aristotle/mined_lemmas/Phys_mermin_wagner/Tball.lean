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

def Tball (L m : ℕ) : Finset (Fin (2 * L + 1)) := Finset.univ.filter fun a => dist1 L a ≤ m

/-- Coordinates at distance exactly `m` from the centre. -/

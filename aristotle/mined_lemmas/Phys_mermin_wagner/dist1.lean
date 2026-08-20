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

def dist1 (L : ℕ) (a : Fin (2 * L + 1)) : ℕ := max ((a : ℕ) - L) (L - (a : ℕ))

/-- The `ℓ^∞` distance of a site to the centre of the box. -/

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

def btgt {d L : ℕ} (p : Site d L × Fin d) : Site d L :=
  Function.update p.1 p.2 (p.1 p.2 + 1)

/-- The spin-wave profile on the box: it rotates the central spin by `π` and vanishes at
distance `R` from the centre. -/

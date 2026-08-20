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

lemma rad_btgt_close {d L : ℕ} {p : Site d L × Fin d} (hp : p ∈ bondSet d L) :
    rad (btgt p) ≤ rad p.1 + 1 ∧ rad p.1 ≤ rad (btgt p) + 1 := by
  constructor
  · exact rad_le_succ fun j => (dist1_btgt hp j).1
  · exact rad_le_succ fun j => (dist1_btgt hp j).2

/-! ### The two energy estimates -/

/-- The bound on the contribution of one bond to the Dirichlet energy. -/

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

lemma rad_le_succ {d L : ℕ} {x y : Site d L} (h : ∀ j, dist1 L (y j) ≤ dist1 L (x j) + 1) :
    rad y ≤ rad x + 1 :=
  Finset.sup_le fun j _ => le_trans (h j) (by
    exact Nat.add_le_add_right (Finset.le_sup (f := fun i => dist1 L (x i)) (Finset.mem_univ j)) 1)

section Shells

variable (d L : ℕ)

/-- Coordinates at distance at most `m` from the centre. -/

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

lemma dist1_btgt {d L : ℕ} {p : Site d L × Fin d} (hp : p ∈ bondSet d L) (j : Fin d) :
    dist1 L (btgt p j) ≤ dist1 L (p.1 j) + 1 ∧ dist1 L (p.1 j) ≤ dist1 L (btgt p j) + 1 := by
  simp only [bondSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  by_cases hj : j = p.2
  · have hlt : p.1 p.2 < Fin.last (2 * L) := by
      rw [Fin.lt_def]
      simpa using hp
    have hval : ((p.1 p.2 + 1 : Fin (2 * L + 1)) : ℕ) = (p.1 p.2 : ℕ) + 1 :=
      Fin.val_add_one_of_lt hlt
    have hbt : btgt p j = p.1 p.2 + 1 := by
      unfold btgt
      rw [hj, Function.update_self]
    rw [hbt, hj]
    unfold dist1
    rw [hval]
    omega
  · have hbt : btgt p j = p.1 j := by
      unfold btgt
      rw [Function.update_of_ne hj]
    rw [hbt]
    omega


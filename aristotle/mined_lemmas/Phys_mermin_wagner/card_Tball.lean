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

lemma card_Tball (L m : ℕ) : (Tball L m).card ≤ 2 * m + 1 := by
  classical
  have : ∀ a ∈ Tball L m, (a : ℕ) + m - L ∈ Finset.range (2 * m + 1) := by
    intro a ha
    simp only [Tball, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [Finset.mem_range]
    unfold dist1 at ha
    omega
  have hinj : ∀ a ∈ Tball L m, ∀ b ∈ Tball L m, (a : ℕ) + m - L = (b : ℕ) + m - L → a = b := by
    intro a ha b hb hab
    simp only [Tball, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    unfold dist1 at ha hb
    have : (a : ℕ) = (b : ℕ) := by omega
    exact Fin.ext this
  calc (Tball L m).card ≤ (Finset.range (2 * m + 1)).card :=
        Finset.card_le_card_of_injOn _ this hinj
    _ = 2 * m + 1 := Finset.card_range _


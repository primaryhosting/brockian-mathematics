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

lemma card_Ecrit (L m : ℕ) : (Ecrit L m).card ≤ 2 := by
  classical
  have hmaps : ∀ a ∈ Ecrit L m, (if (a : ℕ) ≤ L then 0 else 1) ∈ Finset.range 2 := by
    intro a _
    simp only [Finset.mem_range]
    split <;> omega
  have hinj : ∀ a ∈ Ecrit L m, ∀ b ∈ Ecrit L m,
      (if (a : ℕ) ≤ L then 0 else 1) = (if (b : ℕ) ≤ L then 0 else 1) → a = b := by
    intro a ha b hb hab
    simp only [Ecrit, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    unfold dist1 at ha hb
    refine Fin.ext ?_
    by_cases h1 : (a : ℕ) ≤ L <;> by_cases h2 : (b : ℕ) ≤ L <;>
      simp [h1, h2] at hab ⊢ <;> omega
  calc (Ecrit L m).card ≤ (Finset.range 2).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = 2 := Finset.card_range _

/-- The number of sites of the box at `ℓ^∞` distance exactly `m ≥ 1` from the centre is at
most `12 m + 1`, in any dimension `d ≤ 2`. -/

/-
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: verified (axiom-clean: propext, Classical.choice, Quot.sound)
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-- A comparison-based decision tree sorting 4 elements.  A `leaf` outputs a
permutation (the claimed sorted order / ranking of the input), and a `node i j`
compares the input keys at positions `i` and `j` and branches accordingly. -/
inductive DTree where
  | leaf : Equiv.Perm (Fin 4) → DTree
  | node : Fin 4 → Fin 4 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- The worst-case number of comparisons performed by the tree. -/

theorem buildT_spec : ∀ (L : List (Fin 4 × Fin 4)) (ps : Finset (Equiv.Perm (Fin 4)))
    (σ : Equiv.Perm (Fin 4)), σ ∈ ps →
    DTree.run (buildT L ps) σ ∈ ps ∧
      ∀ p ∈ L, (DTree.run (buildT L ps) σ p.1 < DTree.run (buildT L ps) σ p.2 ↔ σ p.1 < σ p.2) := by
  intro L
  induction L with
  | nil =>
      intro ps σ hσ
      refine ⟨?_, by simp⟩
      have hne : ps.Nonempty := ⟨σ, hσ⟩
      simp only [buildT, DTree.run, dif_pos hne]
      exact hne.choose_spec
  | cons p rest ih =>
      obtain ⟨i, j⟩ := p
      intro ps σ hσ
      by_cases hc : σ i < σ j
      · have hmem : σ ∈ ps.filter fun τ => τ i < τ j := by
          simp only [Finset.mem_filter]; exact ⟨hσ, hc⟩
        obtain ⟨h1, h2⟩ := ih (ps.filter fun τ => τ i < τ j) σ hmem
        have hrun : DTree.run (buildT ((i, j) :: rest) ps) σ
            = DTree.run (buildT rest (ps.filter fun τ => τ i < τ j)) σ := by
          simp [buildT, DTree.run, hc]
        rw [Finset.mem_filter] at h1
        refine ⟨by rw [hrun]; exact h1.1, ?_⟩
        intro q hq
        rcases List.mem_cons.1 hq with hq | hq
        · subst hq
          rw [hrun]
          exact iff_of_true h1.2 hc
        · rw [hrun]; exact h2 q hq
      · have hmem : σ ∈ ps.filter fun τ => ¬ τ i < τ j := by
          simp only [Finset.mem_filter]; exact ⟨hσ, hc⟩
        obtain ⟨h1, h2⟩ := ih (ps.filter fun τ => ¬ τ i < τ j) σ hmem
        have hrun : DTree.run (buildT ((i, j) :: rest) ps) σ
            = DTree.run (buildT rest (ps.filter fun τ => ¬ τ i < τ j)) σ := by
          simp [buildT, DTree.run, hc]
        rw [Finset.mem_filter] at h1
        refine ⟨by rw [hrun]; exact h1.1, ?_⟩
        intro q hq
        rcases List.mem_cons.1 hq with hq | hq
        · subst hq
          rw [hrun]
          exact iff_of_false h1.2 hc
        · rw [hrun]; exact h2 q hq

/-- Correct comparison sorts of 4 elements exist, so the lower bound above is
not vacuous. -/

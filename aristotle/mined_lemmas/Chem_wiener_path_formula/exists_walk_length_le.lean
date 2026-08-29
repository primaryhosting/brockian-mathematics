/-
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

namespace Chem

open SimpleGraph Finset

/-- The Wiener index of a finite graph: the sum of the graph distances over all
unordered pairs of vertices (equivalently, half the sum over all ordered pairs). -/

lemma exists_walk_length_le {n : ℕ} :
    ∀ (k : ℕ) (i j : Fin n), Nat.dist i.val j.val ≤ k →
      ∃ w : (pathGraph n).Walk i j, w.length ≤ k := by
  intro k
  induction k with
  | zero =>
      intro i j hij
      have : i = j := by
        apply Fin.ext
        simp only [Nat.dist] at hij
        omega
      subst this
      exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | succ k ih =>
      intro i j hij
      rcases lt_trichotomy i.val j.val with h | h | h
      · have hlt : i.val + 1 < n := lt_of_le_of_lt h j.isLt
        refine ⟨SimpleGraph.Walk.cons (u := i) (v := ⟨i.val + 1, hlt⟩) ?_ ?_, ?_⟩
        · rw [pathGraph_adj]; exact Or.inl rfl
        · exact (ih ⟨i.val + 1, hlt⟩ j (by simp only [Nat.dist] at hij ⊢; omega)).choose
        · have := (ih ⟨i.val + 1, hlt⟩ j (by simp only [Nat.dist] at hij ⊢; omega)).choose_spec
          simpa [SimpleGraph.Walk.length_cons] using this
      · have : i = j := Fin.ext h
        subst this
        exact ⟨SimpleGraph.Walk.nil, by simp⟩
      · have hlt : i.val - 1 < n := lt_of_le_of_lt (Nat.sub_le _ _) i.isLt
        refine ⟨SimpleGraph.Walk.cons (u := i) (v := ⟨i.val - 1, hlt⟩) ?_ ?_, ?_⟩
        · rw [pathGraph_adj]; right; simp only; omega
        · exact (ih ⟨i.val - 1, hlt⟩ j (by simp only [Nat.dist] at hij ⊢; omega)).choose
        · have := (ih ⟨i.val - 1, hlt⟩ j (by simp only [Nat.dist] at hij ⊢; omega)).choose_spec
          simpa [SimpleGraph.Walk.length_cons] using this

/-- The distance between vertices `i` and `j` of the path graph `P n` is `|i - j|`. -/

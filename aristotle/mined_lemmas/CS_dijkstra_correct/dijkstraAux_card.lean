/-
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
We formalize Dijkstra's algorithm on a finite directed graph whose edge weights are
elements of `ℝ≥0∞` (`ENNReal`).  Using `ℝ≥0∞` encodes exactly the two features of the
setting Dijkstra's algorithm requires: weights are **nonnegative**, and a weight of `⊤`
models a missing edge (so unreachable vertices get distance `⊤`).

`CS.gdist w s v` is the true shortest-path distance: the infimum of the costs of all
walks from `s` to `v`.  `CS.dijkstra w s` is the output of the algorithm (the classical
loop: repeatedly select an unvisited vertex of minimal tentative distance, mark it
visited, and relax all of its outgoing edges).  The main theorem `CS.dijkstra_correct`
states that these agree.
-/

namespace CS

open Finset
open scoped ENNReal

section Defs

variable {V : Type*}

/-- `ReachesVia w S s v c` means: there is a walk from `s` to `v` of total weight `c`
all of whose vertices, except possibly the final one, lie in `S`. -/
inductive ReachesVia (w : V → V → ℝ≥0∞) (S : Finset V) (s : V) : V → ℝ≥0∞ → Prop
  | refl : ReachesVia w S s s 0
  | step {u v c} (hu : u ∈ S) (h : ReachesVia w S s u c) :
      ReachesVia w S s v (c + w u v)

/-- The infimum of the weights of walks from `s` to `v` with all intermediate vertices
in `S`. -/

theorem dijkstraAux_card (w : V → V → ℝ≥0∞) (s : V) (n : ℕ) :
    (dijkstraAux w s n).1.card = min n (Fintype.card V) := by
  induction n with
  | zero => simp [dijkstraAux]
  | succ n ih =>
      set p := dijkstraAux w s n with hp
      by_cases h : (p.1ᶜ).Nonempty
      · obtain ⟨u, hu, -, hstep⟩ := dijkstraStep_spec w p h
        have hnew : (dijkstraAux w s (n + 1)).1 = insert u p.1 := by
          rw [show dijkstraAux w s (n + 1) = dijkstraStep w p from rfl, hstep]
        have hlt : p.1.card < Fintype.card V := by
          have : p.1 ≠ Finset.univ := by
            obtain ⟨x, hx⟩ := h
            intro hcon
            simp [hcon] at hx
          exact Finset.card_lt_card (lt_of_le_of_ne (Finset.subset_univ _) this)
        rw [ih] at hlt
        rw [hnew, Finset.card_insert_of_notMem hu, ih]
        omega
      · have hnew : (dijkstraAux w s (n + 1)).1 = p.1 := by
          rw [show dijkstraAux w s (n + 1) = dijkstraStep w p from rfl]
          simp only [dijkstraStep, dif_neg h]
        have huniv : p.1 = Finset.univ := by
          rw [Finset.not_nonempty_iff_eq_empty] at h
          simpa using congrArg (fun t : Finset V => tᶜ) h
        rw [huniv, Finset.card_univ] at ih
        rw [hnew, huniv, Finset.card_univ]
        omega

/-- **Correctness of Dijkstra's algorithm.**  On a finite directed graph with
nonnegative edge weights (weights valued in `ℝ≥0∞`, where `⊤` means "no edge"),
Dijkstra's algorithm computes, for every vertex `v`, the shortest-path distance from
the source `s` to `v`. -/

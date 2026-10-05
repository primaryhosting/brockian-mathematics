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

theorem dijkstraAux_inv (w : V → V → ℝ≥0∞) (s : V) (n : ℕ) :
    Inv w s (dijkstraAux w s n) := by
  induction n with
  | zero =>
      refine ⟨fun v => ?_, fun x hx => absurd hx (by simp [dijkstraAux])⟩
      simp only [dijkstraAux, distVia_empty]
  | succ n ih =>
      obtain ⟨hd, hS⟩ := ih
      set p := dijkstraAux w s n with hp
      by_cases h : (p.1ᶜ).Nonempty
      · obtain ⟨u, hu, hmin, hstep⟩ := dijkstraStep_spec w p h
        have hmin' : ∀ x ∉ p.1, distVia w p.1 s u ≤ distVia w p.1 s x := by
          intro x hx
          have := hmin x hx
          rwa [hd u, hd x] at this
        have hgu : distVia w p.1 s u = gdist w s u := greedy hmin'
        have hrel := relax (u := u) hS
        have hnew : dijkstraAux w s (n + 1) =
            (insert u p.1, fun v => min (p.2 v) (p.2 u + w u v)) := by
          rw [show dijkstraAux w s (n + 1) = dijkstraStep w p from rfl, hstep]
        rw [hnew]
        constructor
        · intro v
          simp only [hrel v, hd v, hd u]
        · intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hxS
          · rw [hrel x, min_eq_left le_self_add, hgu]
          · rw [hrel x, hS x hxS, min_eq_left]
            rw [hgu]
            exact gdist_step
      · have hnew : dijkstraAux w s (n + 1) = p := by
          rw [show dijkstraAux w s (n + 1) = dijkstraStep w p from rfl]
          simp only [dijkstraStep, dif_neg h]
        rw [hnew]
        exact ⟨hd, hS⟩


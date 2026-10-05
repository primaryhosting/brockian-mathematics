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

theorem escape (w : V → V → ℝ≥0∞) (S : Finset V) {s v : V} {c : ℝ≥0∞}
    (h : ReachesVia w Finset.univ s v c) :
    distVia w S s v ≤ c ∨ ∃ x ∉ S, distVia w S s x ≤ c := by
  induction h with
  | refl =>
      by_cases hs : s ∈ S
      · exact Or.inl (by simp [distVia_self])
      · exact Or.inr ⟨s, hs, by simp [distVia_self]⟩
  | @step u v c _ _ ih =>
      rcases ih with hl | ⟨x, hx, hxc⟩
      · by_cases hu : u ∈ S
        · exact Or.inl ((distVia_step hu).trans (by gcongr))
        · exact Or.inr ⟨u, hu, hl.trans le_self_add⟩
      · exact Or.inr ⟨x, hx, hxc.trans le_self_add⟩

/-- Greedy step: an unvisited vertex `u` minimizing the tentative distance already has
its true shortest-path distance as tentative distance. -/

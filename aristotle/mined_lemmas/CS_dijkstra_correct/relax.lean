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

theorem relax {w : V → V → ℝ≥0∞} {S : Finset V} {s u : V}
    (hS : ∀ x ∈ S, distVia w S s x = gdist w s x) (v : V) :
    distVia w (insert u S) s v = min (distVia w S s v) (distVia w S s u + w u v) := by
  refine le_antisymm ?_ ?_
  · refine le_min (distVia_mono (Finset.subset_insert u S)) ?_
    calc distVia w (insert u S) s v
        ≤ distVia w (insert u S) s u + w u v := distVia_step (Finset.mem_insert_self u S)
      _ ≤ distVia w S s u + w u v := by
          gcongr; exact distVia_mono (Finset.subset_insert u S)
  · refine le_distVia fun c hc => ?_
    have key : ∀ {v : V} {c : ℝ≥0∞}, ReachesVia w (insert u S) s v c →
        distVia w S s v ≤ c ∨ distVia w S s u + w u v ≤ c := by
      intro v c hc
      induction hc with
      | refl => exact Or.inl (by simp [distVia_self])
      | @step x v c hx hder ih =>
          rcases Finset.mem_insert.1 hx with rfl | hxS
          · have hxu : distVia w S s x ≤ c := by
              rcases ih with h | h
              · exact h
              · exact le_self_add.trans h
            exact Or.inr (by gcongr)
          · have hx' : distVia w S s x ≤ c := by
              rw [hS x hxS]
              exact distVia_le (hder.mono (Finset.subset_univ _))
            exact Or.inl ((distVia_step hxS).trans (by gcongr))
    rcases key hc with h | h
    · exact le_trans (min_le_left _ _) h
    · exact le_trans (min_le_right _ _) h

/-! ### `gdist` is the infimum of the costs of walks -/

omit [DecidableEq V] in

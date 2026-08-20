import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

variable {V : Type*}

/-! ## Graphs, walks and shortest-path distance

A weighted digraph on the vertex type `V` is given by a weight function
`w : V → V → ℝ≥0∞`.  Weights are nonnegative by construction (this is exactly the
hypothesis Dijkstra's algorithm needs), and the value `⊤` encodes the absence of an edge. -/

/-- `walkCost w a l` is the total weight of the walk that starts at `a` and then visits
the vertices of `l` in order. -/

lemma card_iterate (w : V → V → ℝ≥0∞) (s : V) (k : ℕ) (hk : k ≤ Fintype.card V) :
    (((dijkstraStep w)^[k] (initState s)).1).card = k := by
  induction k with
  | zero => simp [initState]
  | succ k ih =>
      have hcard := ih (le_of_lt (lt_of_lt_of_le (Nat.lt_succ_self k) hk))
      rw [Function.iterate_succ_apply']
      have hne : (Finset.univ \ ((dijkstraStep w)^[k] (initState s)).1).Nonempty := by
        by_contra hcon
        rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hcon
        have huniv : ((dijkstraStep w)^[k] (initState s)).1 = Finset.univ :=
          Finset.eq_univ_of_forall fun x => hcon (Finset.mem_univ x)
        rw [huniv, Finset.card_univ] at hcard
        omega
      have hstep : dijkstraStep w ((dijkstraStep w)^[k] (initState s))
          = (insert (pick ((dijkstraStep w)^[k] (initState s)).2
                ((dijkstraStep w)^[k] (initState s)).1 hne)
              ((dijkstraStep w)^[k] (initState s)).1,
            fun v => min (((dijkstraStep w)^[k] (initState s)).2 v)
              (((dijkstraStep w)^[k] (initState s)).2
                  (pick ((dijkstraStep w)^[k] (initState s)).2
                    ((dijkstraStep w)^[k] (initState s)).1 hne)
                + w (pick ((dijkstraStep w)^[k] (initState s)).2
                    ((dijkstraStep w)^[k] (initState s)).1 hne) v)) := by
        rw [dijkstraStep, dif_pos hne]
      rw [hstep, Finset.card_insert_of_notMem (pick_not_mem _ _ _), hcard]

/-- **Correctness of Dijkstra's algorithm.**  On a finite digraph with nonnegative edge
weights (encoded by `w : V → V → ℝ≥0∞`, where `⊤` marks the absence of an edge), the
distances computed by Dijkstra's algorithm from a source `s` are exactly the shortest-path
distances from `s`. -/

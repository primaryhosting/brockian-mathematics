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

lemma inv_relax (w : V → V → ℝ≥0∞) (s : V) (S : Finset V) (d : V → ℝ≥0∞) (h : Inv w s S d)
    (u : V) (hu : u ∉ S) (hmin : ∀ y ∉ S, d u ≤ d y) :
    Inv w s (insert u S) (fun v => min (d v) (d u + w u v)) := by
  obtain ⟨hA, hB, hC⟩ := h
  have hdu : d u = sdist w s u := greedy w s S d hA hC u hu hmin
  refine ⟨?_, ?_, ?_⟩
  · intro v
    dsimp only
    exact le_min (hA v) (by rw [hdu]; exact sdist_edge w s u v)
  · intro x hx
    dsimp only
    rcases Finset.mem_insert.mp hx with heq | hx
    · rw [heq, min_eq_left le_self_add, hdu]
    · have hle : d x ≤ d u + w u x := by
        rw [hB x hx, hdu]
        exact sdist_edge w s u x
      rw [min_eq_left hle, hB x hx]
  · intro v hv
    have hv1 : v ∉ S := fun hmem => hv (Finset.mem_insert_of_mem hmem)
    dsimp only
    rw [hC v hv1, hdu, Finset.iInf_insert]
    show min (min (if v = s then 0 else ⊤) (⨅ x ∈ S, sdist w s x + w x v))
        (sdist w s u + w u v)
      = min (if v = s then 0 else ⊤)
        (min (sdist w s u + w u v) (⨅ x ∈ S, sdist w s x + w x v))
    rw [min_assoc, min_comm (⨅ x ∈ S, sdist w s x + w x v)]


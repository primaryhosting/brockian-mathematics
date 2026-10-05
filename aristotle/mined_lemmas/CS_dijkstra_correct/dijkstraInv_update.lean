/-
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring, so the
-- required header is repeated as the module docstring just below.)
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-! ## Walks and graph distance

A graph on a vertex type `V` is given by a weight function `w : V → V → ℝ≥0∞`.
Weights live in `ℝ≥0∞`, so they are automatically nonnegative; the value `⊤`
means "no edge".  A walk starting at `u` is a list `l` of the vertices visited
after `u`. -/

section Walks

variable {V : Type*}

/-- The total weight of the walk that starts at `u` and then visits the
vertices of `l` in order. -/

lemma dijkstraInv_update (w : V → V → ℝ≥0∞) (s : V) (S : Finset V) (d : V → ℝ≥0∞)
    (hinv : DijkstraInv w s S d) (u : V) (hu : u ∉ S)
    (hmin : ∀ v : V, v ∉ S → d u ≤ d v) :
    DijkstraInv w s (insert u S) (fun v => min (d v) (d u + w u v)) := by
  have hkey : d u = graphDist w s u := dijkstra_min_eq_dist w s S d hinv u hu hmin
  obtain ⟨h1, h2, h3, h4⟩ := hinv
  have hfix : ∀ a ∈ insert u S, min (d a) (d u + w u a) = d a := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact min_eq_left le_self_add
    · refine min_eq_left ?_
      rw [h2 a ha, hkey]
      exact graphDist_edge_le w s u a
  refine ⟨fun v => ?_, fun v hv => ?_, fun a ha b => ?_, ?_⟩
  · exact le_min (h1 v) (by rw [hkey]; exact graphDist_edge_le w s u v)
  · show min (d v) (d u + w u v) = graphDist w s v
    rw [hfix v hv]
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hkey
    · exact h2 v hv
  · show min (d b) (d u + w u b) ≤ min (d a) (d u + w u a) + w a b
    rw [hfix a ha]
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact min_le_right _ _
    · exact le_trans (min_le_left _ _) (h3 a ha b)
  · show min (d s) (d u + w u s) = 0
    simp [h4]


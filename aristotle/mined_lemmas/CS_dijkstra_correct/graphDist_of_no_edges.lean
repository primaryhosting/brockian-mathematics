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

lemma graphDist_of_no_edges (s v : V) (hsv : v ≠ s) :
    graphDist (fun _ _ => (⊤ : ℝ≥0∞)) s v = ⊤ := by
  refine top_unique (le_iInf fun l => ?_)
  rcases l with ⟨l, hl⟩
  match l, hl with
  | [], hl => exact absurd hl.symm hsv
  | x :: l, _ => simp [walkWeight]

end Walks

/-! ## The algorithm -/

section Algorithm

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- One step of Dijkstra's algorithm: pick an unvisited vertex `u` of minimal
tentative distance, mark it visited, and relax all edges out of `u`. -/

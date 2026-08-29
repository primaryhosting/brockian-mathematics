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

lemma dijkstraInv_step (w : V → V → ℝ≥0∞) (s : V) (st : Finset V × (V → ℝ≥0∞))
    (hinv : DijkstraInv w s st.1 st.2) :
    DijkstraInv w s (dijkstraStep w st).1 (dijkstraStep w st).2 := by
  rw [dijkstraStep]
  split_ifs with hne
  · obtain ⟨humem, humin⟩ := (Finset.exists_min_image st.1ᶜ st.2 hne).choose_spec
    have huS : (Finset.exists_min_image st.1ᶜ st.2 hne).choose ∉ st.1 := by
      simpa using humem
    exact dijkstraInv_update w s st.1 st.2 hinv _ huS
      (fun v hv => humin v (by simpa using hv))
  · exact hinv


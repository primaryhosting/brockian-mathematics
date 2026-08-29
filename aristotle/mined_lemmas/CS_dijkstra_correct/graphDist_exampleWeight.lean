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

lemma graphDist_exampleWeight : graphDist exampleWeight 0 1 = 5 := by
  refine le_antisymm ?_ ?_
  · have h := graphDist_le exampleWeight 0 1 [1] rfl
    simpa [walkWeight, exampleWeight] using h
  · rw [graphDist]
    refine le_iInf fun l => ?_
    obtain ⟨l, hl⟩ := l
    have key : ∀ (l : List (Fin 2)) (x : Fin 2), walkEnd x l = 1 → x = 0 →
        (5 : ℝ≥0∞) ≤ walkWeight exampleWeight x l := by
      intro l
      induction l with
      | nil => intro x he hx; rw [hx] at he; exact absurd he (by decide)
      | cons y l ih =>
          intro x he hx
          subst hx
          simp only [walkWeight]
          fin_cases y
          · simp [exampleWeight]
          · simp [exampleWeight]
    exact key l 0 hl rfl

example : dijkstra exampleWeight 0 1 = 5 := by
  rw [dijkstra_correct, graphDist_exampleWeight]

example : dijkstra exampleWeight 0 0 = 0 := by
  rw [dijkstra_correct, graphDist_self]

end Example

end CS


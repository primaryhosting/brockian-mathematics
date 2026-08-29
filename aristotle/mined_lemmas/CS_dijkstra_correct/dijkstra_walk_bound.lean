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

lemma dijkstra_walk_bound (w : V → V → ℝ≥0∞) (S : Finset V) (d : V → ℝ≥0∞) (u : V)
    (hu : u ∉ S) (hmin : ∀ v : V, v ∉ S → d u ≤ d v)
    (hrelax : ∀ a ∈ S, ∀ b : V, d b ≤ d a + w a b) :
    ∀ (l : List V) (x : V), x ∈ S → walkEnd x l = u → d u ≤ d x + walkWeight w x l := by
  intro l
  induction l with
  | nil =>
      intro x hx he
      simp only [walkEnd] at he
      exact absurd (he ▸ hx) hu
  | cons y l ih =>
      intro x hx he
      simp only [walkEnd] at he
      simp only [walkWeight]
      have hy : d y ≤ d x + w x y := hrelax x hx y
      by_cases hyS : y ∈ S
      · calc d u ≤ d y + walkWeight w y l := ih y hyS he
          _ ≤ (d x + w x y) + walkWeight w y l := by gcongr
          _ = d x + (w x y + walkWeight w y l) := by rw [add_assoc]
      · calc d u ≤ d y := hmin y hyS
          _ ≤ d x + w x y := hy
          _ ≤ d x + (w x y + walkWeight w y l) := by
              gcongr
              exact le_self_add

omit [Fintype V] in
/-- Key step: an unvisited vertex of minimal tentative distance already carries
its true distance. -/

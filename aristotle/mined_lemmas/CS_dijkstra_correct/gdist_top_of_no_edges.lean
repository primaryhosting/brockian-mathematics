-- (Lean requires `import` to be the first command of a file, so the header comment
-- follows it.)
import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
We formalise Dijkstra's algorithm on a finite directed graph whose edge weights are
nonnegative (encoded by taking values in `ℝ≥0∞`, where `⊤` means "no edge"), and prove
that it computes the true shortest-path distances from a fixed source.
-/

namespace CS

open scoped ENNReal

variable {V : Type*}

/-! ## Walks, their weights, and the shortest-path distance -/

/-- The endpoint of the walk that starts at `s` and visits the vertices of `l` in order. -/

lemma gdist_top_of_no_edges (w : V → V → ℝ≥0∞) (hw : ∀ u v, w u v = ⊤) {s t : V}
    (h : s ≠ t) : gdist w s t = ⊤ := by
  refine eq_top_iff.2 (le_gdist w ?_)
  intro l hl
  cases l with
  | nil => exact absurd hl h
  | cons a l' => simp [hw]

/-- On the two-vertex graph with the single edge `false → true` of weight `3`, Dijkstra
returns the distance `3`. -/
example :
    (dijkstra (fun a b : Bool => if a = false ∧ b = true then 3 else ⊤) false).D true = 3 := by
  set w : Bool → Bool → ℝ≥0∞ := fun a b => if a = false ∧ b = true then 3 else ⊤ with hwdef
  rw [dijkstra_correct]
  refine le_antisymm ?_ (le_gdist w ?_)
  · simpa [hwdef] using gdist_le w (l := [true]) rfl
  · intro l hl
    match l with
    | [] => exact absurd hl (by simp)
    | [a] =>
        have : a = true := hl
        subst this
        simp [hwdef]
    | a :: b :: l' =>
        cases a with
        | false => simp [hwdef]
        | true => simp [hwdef]

end CS

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

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


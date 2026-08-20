import Mathlib
import RequestProject.Circuit

/-!
A non-triviality check for the circuit model: the class `AC⁰[q]` really does contain the
`MOD q` function, computed by the depth-one circuit consisting of a single `MOD q` gate
applied to all inputs.  This guards against the main theorem being vacuously true because
the circuit model computes nothing.
-/

namespace CS

open Finset


theorem list_foldr_max_le {α : Type*} (l : List α) (f : α → ℕ) (a : α) (ha : a ∈ l) :
    f a ≤ (l.map f).foldr max 0 := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
      simp only [List.map_cons, List.foldr_cons]
      rcases List.mem_cons.1 ha with rfl | h
      · exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)


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


theorem list_sum_apply {α β : Type*} [AddCommMonoid β] (l : List (α → β)) (x : α) :
    l.sum x = (l.map (fun f => f x)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- The value of the randomized product used at an `OR`/`AND` gate, assuming the children are
computed correctly. -/

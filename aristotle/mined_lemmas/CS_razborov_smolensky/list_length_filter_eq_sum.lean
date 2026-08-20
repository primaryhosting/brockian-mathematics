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


theorem list_length_filter_eq_sum {α : Type*} (l : List α) (w : α → Bool) :
    (l.filter w).length = (l.map (fun a => if w a then 1 else 0)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => cases h : w a <;> simp [h, ih, add_comm]


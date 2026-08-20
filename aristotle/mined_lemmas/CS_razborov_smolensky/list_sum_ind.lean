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


theorem list_sum_ind {F : Type*} [Field F] {k : ℕ} (L : List (Fin k)) (w : Fin k → Bool) :
    (L.map (fun j => ind F (w j))).sum = ((L.filter w).length : F) := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons, ih, List.filter_cons]
      cases h : w a <;> simp [ind, add_comm]


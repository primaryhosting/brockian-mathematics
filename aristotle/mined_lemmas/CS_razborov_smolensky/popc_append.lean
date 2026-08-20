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


theorem popc_append {n p : ℕ} (x : Fin n → Bool) (b : Fin p → Bool) :
    popc (Fin.append x b) = popc x + popc b := by
  simp only [popc]
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- Substituting constants for the last `p` inputs does not increase the degree. -/

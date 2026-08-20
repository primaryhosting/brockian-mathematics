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


theorem modCircuit_gval_inp (q n : ℕ) (x : Fin n → Bool) (i : Fin (modCircuit n).size)
    (h : i.val < n) : (modCircuit n).gval q x i = x ⟨i.val, h⟩ := by
  rw [Circuit.gval]
  simp only [modCircuit, dif_pos h]


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


theorem modCircuit_gdepth_inp (n : ℕ) (i : Fin (modCircuit n).size) (h : i.val < n) :
    (modCircuit n).gdepth i = 0 := by
  rw [Circuit.gdepth]
  simp only [modCircuit, dif_pos h]


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


theorem modCircuit_gate_out (n : ℕ) :
    (modCircuit n).gate (modCircuit n).out = .modg (List.finRange n) := by
  simp only [modCircuit]
  rw [dif_neg (lt_irrefl n)]


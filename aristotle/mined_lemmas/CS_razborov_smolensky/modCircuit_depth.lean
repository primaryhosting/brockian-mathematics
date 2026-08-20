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


theorem modCircuit_depth (n : ℕ) : (modCircuit n).depth = 1 := by
  rw [Circuit.depth, Circuit.gdepth, modCircuit_gate_out]
  simp only []
  rw [foldr_max_eq_zero _ ?_]
  intro a ha
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha
  exact modCircuit_gdepth_inp n _ j.isLt

/-- Non-triviality check: the class `AC⁰[q]` contains the `MOD q` function. -/

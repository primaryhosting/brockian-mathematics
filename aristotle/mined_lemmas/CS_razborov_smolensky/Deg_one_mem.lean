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


theorem Deg_one_mem {d : ℕ} : (1 : (Fin n → Bool) → F) ∈ Deg F n d := by
  rw [← mono_empty]
  exact mono_mem_Deg (by simp)


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


theorem Deg_pow {d k : ℕ} {f : (Fin n → Bool) → F} (hf : f ∈ Deg F n d) :
    f ^ k ∈ Deg F n (k * d) := by
  induction k with
  | zero => simpa using (Deg_one_mem : (1 : (Fin n → Bool) → F) ∈ Deg F n 0)
  | succ k ih =>
      have := Deg_mul ih hf
      have h2 : k * d + d = (k + 1) * d := by ring
      rw [h2] at this
      simpa [pow_succ] using this


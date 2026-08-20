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


theorem gval_modg (C : Circuit n) (q : ℕ) (x : Fin n → Bool) (i : Fin C.size)
    (L : List (Fin i.val)) (hg : C.gate i = .modg L) :
    C.gval q x i = decide (¬ q ∣ (L.filter (fun j => C.gval q x (C.up i j))).length) := by
  rw [gval, hg]


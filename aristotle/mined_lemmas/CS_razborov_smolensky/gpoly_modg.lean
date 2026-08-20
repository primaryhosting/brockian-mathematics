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


theorem gpoly_modg (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) (ρ : Rand C t)
    (i : Fin C.size) (L : List (Fin i.val)) (hg : C.gate i = .modg L) :
    gpoly F C q t ρ i = ((L.map (fun j => gpoly F C q t ρ (C.up i j))).sum) ^ (q - 1) := by
  rw [gpoly, hg]


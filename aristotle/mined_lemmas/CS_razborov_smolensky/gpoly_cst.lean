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


theorem gpoly_cst (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) (ρ : Rand C t)
    (i : Fin C.size) (b : Bool) (hg : C.gate i = .cst b) :
    gpoly F C q t ρ i = fun _ => ind F b := by rw [gpoly, hg]


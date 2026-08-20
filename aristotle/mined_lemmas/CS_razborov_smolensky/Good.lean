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


def Good (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) (ρ : Rand C t) (x : Fin n → Bool)
    (i : Fin C.size) : Prop := gpoly F C q t ρ i x = ind F (C.gval q x i)

/-- Gate `i` does not introduce an error: if all its children are correct, so is it. -/

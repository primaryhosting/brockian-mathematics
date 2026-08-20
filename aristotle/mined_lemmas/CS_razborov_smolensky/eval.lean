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


noncomputable def eval (C : Circuit n) (q : ℕ) (x : Fin n → Bool) : Bool := C.gval q x C.out

/-- The depth of the circuit. -/

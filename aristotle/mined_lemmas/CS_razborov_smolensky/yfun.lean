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


def yfun (ζ : F) (i : Fin n) : (Fin n → Bool) → F := fun x => if x i then ζ else 1

/-- `x ↦ ∏_{i ∈ S} ζ ^ (x i)`. -/

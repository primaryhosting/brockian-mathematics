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


def popc {n : ℕ} (x : Fin n → Bool) : ℕ := ∑ i, (if x i then 1 else 0)

/-- The `MOD p` function: `true` iff the number of ones is *not* divisible by `p`. -/

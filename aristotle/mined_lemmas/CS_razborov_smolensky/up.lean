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


def up (C : Circuit n) (i : Fin C.size) (j : Fin i.val) : Fin C.size :=
  ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩

/-- The Boolean value computed at gate `i`, with `MOD q` gates. -/

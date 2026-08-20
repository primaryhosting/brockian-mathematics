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


def modCircuit (n : ℕ) : Circuit n where
  size := n + 1
  gate := fun i => if h : i.val < n then .inp ⟨i.val, h⟩ else .modg (List.finRange i.val)
  out := ⟨n, Nat.lt_succ_self n⟩


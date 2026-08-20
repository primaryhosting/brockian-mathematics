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


theorem modFun_self_mem_AC0mod (q : ℕ) : InAC0mod q (ModFun q) := by
  refine ⟨1, 1, 1, fun n => ⟨modCircuit n, ?_, ?_, fun x => modCircuit_eval q n x⟩⟩
  · simp [modCircuit]
  · rw [modCircuit_depth]

end CS

import Mathlib

/-!
Counting lemmas used in the proof of Razborov's approximation lemma.

The main statement is `CS.card_gate_bad_le`: if a nonempty set `S` of children of a gate
carries a "witness" `j₀` with `w j₀ = true`, then the set of random choices `ρ` for which
*every* one of the `t` random restrictions at that gate selects a multiple of `q` many
witnesses has density at most `2^{-t}`.
-/

namespace CS

open Finset
open scoped Classical

/-- Counting functions `ι → β` by the value at a single coordinate. -/

import Mathlib

/-!
# Deutsch's algorithm

We formalise Deutsch's algorithm for a function `f : Bool → Bool` on one bit.

The two-qubit state space is modelled by amplitude functions `Bool → Bool → ℂ`
(the first argument is the "query" qubit, the second the "answer" qubit).

The circuit is

  |0⟩|1⟩  →  (H ⊗ H)  →  U_f  →  (H ⊗ I)  →  measure the first qubit,

where the oracle `U_f |x,y⟩ = |x, y ⊕ f x⟩` is applied **exactly once**
(the definition `QC.deutschFinal` contains a single occurrence of `QC.oracle f`,
and `f` occurs nowhere else in the circuit).

The main result `QC.deutsch_correct` states that measuring the first qubit
returns `false` with probability `1` iff `f` is constant, and `true` with
probability `1` iff `f` is balanced (`f false ≠ f true`).
-/

namespace QC

open Complex

/-- The scalar `1/√2` used by the Hadamard gate. -/

def initState : Bool → Bool → ℂ :=
  fun x y => if x = false ∧ y = true then 1 else 0

/-- The state at the end of Deutsch's circuit.  The oracle is queried once. -/

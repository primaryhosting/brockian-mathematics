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

theorem deutschProb_true_eq_one_iff (f : Bool → Bool) :
    deutschProb f true = 1 ↔ f false ≠ f true := by
  constructor
  · intro h hc
    rw [((deutsch_correct f).1 hc).2] at h
    norm_num at h
  · intro h
    exact ((deutsch_correct f).2 h).1

end QC

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false


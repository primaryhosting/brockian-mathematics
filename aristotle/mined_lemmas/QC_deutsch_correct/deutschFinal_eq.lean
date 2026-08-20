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

lemma deutschFinal_eq (f : Bool → Bool) (x y : Bool) :
    deutschFinal f x y =
      isqrt2 * (1 / 2) * sign y * (sign (f false) + sign x * sign (f true)) := by
  simp only [deutschFinal, hFirst, hSecond, oracle, initState, sign]
  cases x <;> cases y <;> cases hf : f false <;> cases ht : f true <;>
    simp [isqrt2_mul_isqrt2] <;> ring_nf

/-- **Deutsch's algorithm is correct.**  With a single query to the oracle
`U_f`, measuring the first qubit of the final state yields `false` with
probability `1` when `f` is constant, and `true` with probability `1` when `f`
is balanced. -/

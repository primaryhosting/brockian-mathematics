/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to precede any module docstring, so the header above is
-- repeated as the module docstring immediately after the import.)

import Mathlib

/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Gottesman–Knill

We formalise the Gottesman–Knill theorem: a quantum circuit built out of Clifford gates
(Hadamard, phase, CNOT) acting on `n` qubits can be simulated classically with only
`2n + 2` bits of memory and a constant amount of work per gate, in the Heisenberg picture.

The `2^n`-dimensional Hilbert space is modelled as `Bits n → ℂ`, i.e. operators are
matrices indexed by bitstrings `Bits n = Fin n → Bool`.

A Pauli operator is stored as a *tableau row* `(k, x, z)` with `k : ZMod 4` a phase
exponent and `x z : Bits n`; it denotes the operator `i^k X^x Z^z`, whose matrix is
`|b⟩ ↦ i^k (-1)^{z·b} |b ⊕ x⟩`.

The three main ingredients are:

* `QI.gateMat_unitary` : the gate matrices are unitary;
* `QI.gate_conj` : conjugating a Pauli matrix by a Clifford gate matrix is computed
  exactly by the (purely classical, bit-level) tableau update `QI.gateConj`;
* `QI.gateConj_local` : the tableau update only touches the qubits in the gate's support.

Together these give `QI.gottesman_knill`.
-/

namespace QI

/-- Bitstrings of length `n`; these index the computational basis of `n` qubits. -/
abbrev Bits (n : ℕ) : Type := Fin n → Bool

/-- Bitwise XOR of two bitstrings. -/

lemma expectation_eq {n : ℕ} (C : Circuit n) (P : Pauli n) :
    ((circuitMat C)ᴴ * P.toMatrix * circuitMat C) (zeroBits n) (zeroBits n)
      = if (circuitConj C P).x = zeroBits n then iPow (circuitConj C P).k else 0 := by
  rw [circuit_conj, toMatrix_zero_zero]

/-! ### The Gottesman–Knill theorem -/

/-- **Gottesman–Knill.** Stabilizer (Clifford) circuits are efficiently classically
simulable.

For `n` qubits the quantum state space has dimension `2 ^ n`, but the classical simulator
keeps only a tableau row `Pauli n`, a state space of size `4 · 4 ^ n`, i.e. `2n + 2` bits.

1. `circuitMat C` is unitary, so a circuit is a genuine quantum evolution.
2. The Heisenberg evolution `U(C)† P U(C)` of any Pauli observable `P` is computed exactly
   by the purely classical tableau fold `circuitConj C`.
3. Each gate's update is *local*: it touches only the (at most two) qubits in the gate's
   support, so simulating a circuit of `m` gates costs `O(m)` bit operations on top of
   the `O(n)` sized tableau.
4. Consequently the expectation value `⟨0…0| U(C)† P U(C) |0…0⟩` — which determines the
   statistics of any Pauli measurement on the output state — is read off from the
   simulated tableau in `O(n)` time. -/

/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Matrix

namespace QI

/-! ## Bit vectors -/

/-- Computational basis labels for `n` qubits: bit strings of length `n`. -/
abbrev Bits (n : ℕ) := Fin n → Bool

variable {n : ℕ}

/-- Bitwise `xor` of two bit strings. -/

lemma stepGate_local (g : Gate n) (p : Pauli n) (i : Fin n) (hi : i ∉ support g) :
    (stepGate g p).xs i = p.xs i ∧ (stepGate g p).zs i = p.zs i := by
  cases g with
  | H j =>
      simp only [support, Finset.mem_singleton] at hi
      constructor <;> simp [stepGate, hi]
  | S j =>
      simp only [support, Finset.mem_singleton] at hi
      constructor <;> simp [stepGate, hi]
  | CX j k h =>
      simp only [support, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      constructor <;> simp [stepGate, cxf, czf, hi.1, hi.2]

/-! ## The Gottesman–Knill theorem -/

/--
**Gottesman–Knill.**  Stabilizer (Clifford) circuits are efficiently classically simulable.

Concretely, for every circuit `C` built from the Clifford generators `H`, `S`, `CNOT` on `n`
qubits, the purely classical tableau update `simulate C : Pauli n → Pauli n`, which stores only
`2n + 2` bits per Pauli operator, reproduces the Heisenberg evolution of every Pauli operator
under the (genuinely `2^n`-dimensional, unitary) circuit matrix `circuitMat C`:

1. `circuitMat C` is unitary;
2. `circuitMat C • P • (circuitMat C)† = simulate C P` for every Pauli `P`;
3. each classical gate step alters the tableau only in the (at most two) coordinates the gate
   acts on, and leaves the rest untouched — so simulating `m` gates on a stabilizer state given
   by `n` Pauli generators costs `O(n·m)` elementary bit operations;
4. consequently stabilizers are propagated: if `P` stabilizes a state `v`, then `simulate C P`
   stabilizes the evolved state `circuitMat C v`.
-/

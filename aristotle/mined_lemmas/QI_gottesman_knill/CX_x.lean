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

lemma CX_x {n : ℕ} {c t : Fin n} (hct : c ≠ t) (b x : Bits n) :
    bxor (flipT c t b) x = flipT c t (bxor b (Function.update x t (xor (x t) (x c)))) := by
  funext i
  rcases eq_or_ne i t with hi | hi
  · rw [hi]
    show xor (flipT c t b t) (x t)
        = flipT c t (bxor b (Function.update x t (xor (x t) (x c)))) t
    rw [flipT_at, flipT_at]
    show xor (xor (b t) (b c)) (x t)
        = xor (xor (b t) (Function.update x t (xor (x t) (x c)) t))
              (xor (b c) (Function.update x t (xor (x t) (x c)) c))
    rw [Function.update_self, Function.update_of_ne hct]
    cases b t <;> cases b c <;> cases x t <;> cases x c <;> simp
  · show xor (flipT c t b i) (x i)
        = flipT c t (bxor b (Function.update x t (xor (x t) (x c)))) i
    rw [flipT_ne c t b hi, flipT_ne c t _ hi]
    show xor (b i) (x i) = xor (b i) (Function.update x t (xor (x t) (x c)) i)
    rw [Function.update_of_ne hi]


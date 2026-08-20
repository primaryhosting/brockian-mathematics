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

lemma CX_bdot {n : ℕ} {c t : Fin n} (h : c ≠ t) (z b : Bits n) :
    bdot z (flipT c t b) = bdot (Function.update z c (xor (z c) (z t))) b := by
  have hoff1 : bdotOff2 c t z (flipT c t b) = bdotOff2 c t z b :=
    bdotOff2_congr c t (fun _ _ _ => rfl) (fun i _ hi => flipT_ne c t b hi)
  have hoff2 : bdotOff2 c t (Function.update z c (xor (z c) (z t))) b = bdotOff2 c t z b :=
    bdotOff2_congr c t (fun i hc _ => Function.update_of_ne hc _ _) (fun _ _ _ => rfl)
  rw [bdot_eq_off2 h z (flipT c t b), bdot_eq_off2 h _ b, hoff1, hoff2,
    flipT_ne c t b h, flipT_at c t b, Function.update_self, Function.update_of_ne (Ne.symm h)]
  have key : ∀ p q r s : Bool, (cond (p && r) (1 : ZMod 2) 0) + cond (q && (xor s r)) 1 0
      = cond ((xor p q) && r) 1 0 + cond (q && s) 1 0 := by decide
  rw [key]

/-- The `X`-part identity behind the `CNOT` tableau rule. -/

/-
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Statement: The 7-qubit Steane (CSS) code corrects any single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Statement: The 7-qubit Steane (CSS) code corrects any single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Basic setting: 7 qubits, computational basis indexed by bit strings -/

/-- Labels of the computational basis of `(ℂ²)^{⊗7}`: bit strings of length 7. -/
abbrev Bits := Fin 7 → ZMod 2

/-- Syndrome values: three bits (one per parity check of each CSS type). -/
abbrev Chk := Fin 3 → ZMod 2

/-- A state of the 7-qubit register, in the computational basis. -/
abbrev State := Bits → ℂ

/-- Mod-2 inner product of two bit strings. -/

lemma steane_recovery_pauli (v w : Bits) (hvw : IsSingleQubit v w) (psi : State) :
    Rec (decode (syn v)) (decode (syn w)) (Err v w psi) = psi := by
  obtain ⟨i, hi⟩ := hvw
  have hv : decode (syn v) = v :=
    decode_syn_of_weight_le_one v ⟨i, fun j hj => (hi j hj).1⟩
  have hw : decode (syn w) = w :=
    decode_syn_of_weight_le_one w ⟨i, fun j hj => (hi j hj).2⟩
  rw [hv, hw, Rec_Err]

/-- **The Steane code corrects any single-qubit error.**
Let `ψ` be any state of the Steane code space and let `E_{v,w}` be any Pauli error acting
on at most one of the seven qubits.  Then:

* measuring the three `Z`-type stabilizers of the code on the corrupted state `E_{v,w} ψ`
  is deterministic and returns the syndrome bits `(H v)_k`;
* measuring the three `X`-type stabilizers is deterministic and returns the syndrome bits
  `(H w)_k`;
* the recovery operator obtained by Hamming-decoding *only these six measured syndrome
  bits* restores the original code state `ψ` exactly.

Since the four Pauli operators at a given qubit span all one-qubit operators, this is the
usual discretization statement of single-qubit error correction; the version for an
arbitrary (non-Pauli) one-qubit error is `QI.steane_code_arbitrary_error` below. -/

/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace QI

/-! ## Basic types

A computational basis state of one *block* of three qubits is a function `Fin 3 → Bool`;
a computational basis state of the nine qubits of the Shor code is a function
`Fin 3 → Blk`, i.e. three blocks of three qubits.  A qubit is addressed by a pair
`q : Q = Fin 3 × Fin 3` (block index, position inside the block). -/

/-- Computational basis states of one three-qubit block. -/
abbrev Blk := Fin 3 → Bool

/-- Computational basis states of the nine qubits. -/
abbrev Bas := Fin 3 → Blk

/-- Addresses of the nine qubits. -/
abbrev Q := Fin 3 × Fin 3

/-- Bitwise `xor` on a block. -/

lemma ip_cw_pauli (s t : Bool) (x z : Bas) :
    ip (cw s) (PauliOp x z (cw t)) = ((∏ j, gBlk s t (x j) (z j) : ℤ) : ℂ) := by
  rw [← ip_cw_pauli_int]
  simp only [ip, PauliOp, cw]
  push_cast
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [mul_assoc]

/-! ## Weight of a Pauli operator -/

/-- Number of qubits of a block on which the Pauli operator `(u, w)` acts nontrivially. -/

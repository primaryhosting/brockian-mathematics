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

lemma wt_bitP_le_two (xb zb xb' zb' : Bool) (q q' : Q) :
    wt (bxorb (bitP xb q) (bitP xb' q')) (bxorb (bitP zb q) (bitP zb' q')) ≤ 2 := by
  refine wt_le_two_of_supp _ _ q q' fun p hp hp' => ?_
  constructor <;>
    simp [bxorb, bxorB, bitP_apply_ne _ _ _ hp, bitP_apply_ne _ _ _ hp']

/-! ## Knill–Laflamme for pairs of Pauli operators of small support -/


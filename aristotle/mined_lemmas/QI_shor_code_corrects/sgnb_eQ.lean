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

lemma sgnb_eQ (q : Q) (b : Bas) : sgnb (eQ q) b = if b q.1 q.2 then -1 else 1 := by
  rw [sgnb, Finset.prod_eq_single q.1]
  · have : eQ q q.1 = eBlk q.2 := by
      funext k; simp [eQ, eBlk]
    rw [this, sgnB_eBlk]
  · intro j _ hj
    have : eQ q j = zeroB := by
      funext k; simp [eQ, zeroB, hj]
    rw [this, sgnB_zero]
  · intro h; exact absurd (Finset.mem_univ q.1) h

/-- The coefficients expressing a `2 × 2` matrix in the (phase-free) Pauli basis. -/

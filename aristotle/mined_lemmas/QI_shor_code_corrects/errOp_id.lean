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

lemma errOp_id (q : Q) (ψ : Bas → ℂ) :
    errOp q (fun u v => if u = v then 1 else 0) ψ = ψ := by
  funext b
  have h : upd b q (b q.1 q.2) = b := upd_self b q
  simp only [errOp, Fintype.sum_bool]
  cases hb : b q.1 q.2 <;> rw [hb] at h <;> simp [h]

/-- The restriction to *single*-qubit errors is essential: the weight-three Pauli operator
consisting of one `Z` in each block (the logical `X` of the Shor code) maps `|1_L⟩` to a state
with a nonzero overlap with `|0_L⟩`, so it violates the Knill–Laflamme condition. -/

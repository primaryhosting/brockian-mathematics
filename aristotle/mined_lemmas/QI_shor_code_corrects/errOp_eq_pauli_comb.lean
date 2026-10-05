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

lemma errOp_eq_pauli_comb (q : Q) (A : Bool → Bool → ℂ) (ψ : Bas → ℂ) :
    errOp q A ψ
      = fun b => ∑ xb : Bool, ∑ zb : Bool,
          paCoef A xb zb * PauliOp (bitP xb q) (bitP zb q) ψ b := by
  funext b
  have hz : PauliOp (bitP false q) (bitP false q) ψ b = ψ b := by
    simp [PauliOp]
  have hZ : PauliOp (bitP false q) (bitP true q) ψ b
      = (if b q.1 q.2 then (-1 : ℂ) else 1) * ψ b := by
    simp only [PauliOp, bitP_false, bitP_true, sgnb_eQ, bxorb_zero_left]
    split <;> norm_num
  have hX : PauliOp (bitP true q) (bitP false q) ψ b = ψ (bxorb (eQ q) b) := by
    simp [PauliOp]
  have hXZ : PauliOp (bitP true q) (bitP true q) ψ b
      = (if b q.1 q.2 then (-1 : ℂ) else 1) * ψ (bxorb (eQ q) b) := by
    simp only [PauliOp, bitP_true, sgnb_eQ]
    split <;> norm_num
  simp only [errOp, Fintype.sum_bool, hz, hZ, hX, hXZ, paCoef]
  cases hb : b q.1 q.2
  · have h1 : upd b q false = b := by rw [← hb]; exact upd_self b q
    have h2 : upd b q true = bxorb (eQ q) b := by
      have := upd_not b q; rw [hb] at this; simpa using this
    have hif : (if (false : Bool) = true then (-1 : ℂ) else 1) = 1 := by norm_num
    rw [h1, h2, hif]
    ring
  · have h1 : upd b q true = b := by rw [← hb]; exact upd_self b q
    have h2 : upd b q false = bxorb (eQ q) b := by
      have := upd_not b q; rw [hb] at this; simpa using this
    have hif : (if (true : Bool) = true then (-1 : ℂ) else 1) = -1 := by norm_num
    rw [h1, h2, hif]
    ring

/-! ## Errors on one or two qubits have weight at most two -/


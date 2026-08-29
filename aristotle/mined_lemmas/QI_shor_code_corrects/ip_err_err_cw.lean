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

lemma ip_err_err_cw (q q' : Q) (A A' : Bool → Bool → ℂ) (s t : Bool) :
    ip (errOp q A (cw s)) (errOp q' A' (cw t))
      = if s = t then ip (errOp q A (cw false)) (errOp q' A' (cw false)) else 0 := by
  have hexp : ∀ r r' : Bool, ip (errOp q A (cw r)) (errOp q' A' (cw r'))
      = ∑ xb : Bool, ∑ zb : Bool, ∑ xb' : Bool, ∑ zb' : Bool,
          (starRingEnd ℂ) (paCoef A xb zb) * (paCoef A' xb' zb' *
            ip (PauliOp (bitP xb q) (bitP zb q) (cw r))
               (PauliOp (bitP xb' q') (bitP zb' q') (cw r'))) := by
    intro r r'
    rw [errOp_eq_pauli_comb, errOp_eq_pauli_comb]
    simp only [Fintype.sum_bool, ip_add_left, ip_add_right, ip_smul_left, ip_smul_right]
    ring
  rw [hexp s t]
  by_cases hst : s = t
  · rw [if_pos hst, hexp false false]
    refine Finset.sum_congr rfl fun xb _ => Finset.sum_congr rfl fun zb _ =>
      Finset.sum_congr rfl fun xb' _ => Finset.sum_congr rfl fun zb' _ => ?_
    rw [ip_pauli_cw _ _ _ _ (wt_bitP_le_two xb zb xb' zb' q q') s t, if_pos hst]
  · rw [if_neg hst]
    refine Finset.sum_eq_zero fun xb _ => Finset.sum_eq_zero fun zb _ =>
      Finset.sum_eq_zero fun xb' _ => Finset.sum_eq_zero fun zb' _ => ?_
    rw [ip_pauli_cw _ _ _ _ (wt_bitP_le_two xb zb xb' zb' q q') s t, if_neg hst]
    ring

/-! ## Normalisation -/


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

lemma errOp_smul (q : Q) (A : Bool → Bool → ℂ) (k : ℂ) (ψ : Bas → ℂ) :
    errOp q A (fun b => k * ψ b) = fun b => k * errOp q A ψ b := by
  funext b
  simp only [errOp, Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => by ring

/-! ## Main theorem -/

/-- **The nine-qubit Shor code corrects an arbitrary single-qubit error.**

The two logical states `|0_L⟩`, `|1_L⟩` (`shorCodeword false`, `shorCodeword true`) are
orthonormal, and for *any* two single-qubit operators `A` at qubit `q` and `A'` at qubit `q'`
(these span all errors acting on a single, arbitrary, unknown qubit) the Knill–Laflamme
error-correction conditions hold:
`⟨i_L| E† F |j_L⟩ = α δ_{ij}` with a constant `α` depending only on the errors, not on the
encoded state.  By the Knill–Laflamme theorem this is exactly the statement that the code
corrects the corresponding error set, i.e. an arbitrary error on one qubit. -/

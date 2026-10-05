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

lemma sgnB_eBlk (k₀ : Fin 3) (β : Blk) : sgnB (eBlk k₀) β = if β k₀ then -1 else 1 := by
  revert k₀ β; decide

/-! ## The Shor codewords

The (unnormalised) logical states are
`|0_L⟩ = (|000⟩+|111⟩)^{⊗3}` and `|1_L⟩ = (|000⟩-|111⟩)^{⊗3}`,
whose amplitudes in the computational basis are integers. -/

/-- Amplitude, on one block, of `|000⟩ + |111⟩` (`s = false`) resp. `|000⟩ - |111⟩` (`s = true`). -/

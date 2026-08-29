import Mathlib

/-!
# Toffoli Unitary
Category: Quantum Computing
Target: QC.toffoli_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The Toffoli (CCNOT) gate acts on three qubits: it flips the target qubit exactly when
both control qubits are `1`.  In the computational basis `|abc⟩`, indexed by
`i = 4a + 2b + c : Fin 8`, this is the transposition of the basis states
`|110⟩ = 6` and `|111⟩ = 7`, i.e. the permutation matrix of `Equiv.swap 6 7`.

We record that this matrix is a permutation matrix, that it is its own inverse,
and that it is unitary.  The unitarity uses Mathlib's
`Matrix.conjTranspose_permMatrix` and `Matrix.permMatrix_mul`.
-/

namespace QC

open Matrix

/-- The permutation of the eight computational basis states of three qubits
induced by the Toffoli (CCNOT) gate: it exchanges `|110⟩` and `|111⟩`. -/

theorem toffoli_mulVec_single (i : Fin 8) :
    toffoli *ᵥ (Pi.single i (1 : ℂ)) = Pi.single (toffoliPerm.symm i) (1 : ℂ) := by
  ext k
  simp [toffoli, Pi.single_apply, Equiv.apply_eq_iff_eq_symm_apply]

/-- The Toffoli gate is an involution: it is its own inverse. -/

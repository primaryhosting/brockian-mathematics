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
def toffoliPerm : Equiv.Perm (Fin 8) := Equiv.swap 6 7

/-- The Toffoli (CCNOT) matrix, as the permutation matrix of `QC.toffoliPerm`. -/
noncomputable def toffoli : Matrix (Fin 8) (Fin 8) ℂ := toffoliPerm.permMatrix ℂ

/-- Entrywise description of the Toffoli matrix. -/
theorem toffoli_apply (i j : Fin 8) :
    toffoli i j = if toffoliPerm i = j then 1 else 0 := by
  simp [toffoli, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

/-- The Toffoli matrix, written out explicitly as an `8 × 8` matrix. -/
theorem toffoli_eq_explicit :
    toffoli = !![1, 0, 0, 0, 0, 0, 0, 0;
                 0, 1, 0, 0, 0, 0, 0, 0;
                 0, 0, 1, 0, 0, 0, 0, 0;
                 0, 0, 0, 1, 0, 0, 0, 0;
                 0, 0, 0, 0, 1, 0, 0, 0;
                 0, 0, 0, 0, 0, 1, 0, 0;
                 0, 0, 0, 0, 0, 0, 0, 1;
                 0, 0, 0, 0, 0, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toffoli_apply, toffoliPerm, Equiv.swap_apply_def]

/-- The Toffoli gate maps the computational basis state `|i⟩` to `|toffoliPerm i⟩`;
in particular it flips the third qubit exactly when the first two are `1`. -/
theorem toffoli_mulVec_single (i : Fin 8) :
    toffoli *ᵥ (Pi.single i (1 : ℂ)) = Pi.single (toffoliPerm.symm i) (1 : ℂ) := by
  ext k
  simp [toffoli, Pi.single_apply, Equiv.apply_eq_iff_eq_symm_apply]

/-- The Toffoli gate is an involution: it is its own inverse. -/
theorem toffoli_mul_self : toffoli * toffoli = 1 := by
  have h : toffoliPerm * toffoliPerm = 1 := by
    simp [toffoliPerm, Equiv.swap_mul_self]
  rw [toffoli, ← permMatrix_mul, h, permMatrix_one]

/-- **The Toffoli (CCNOT) matrix is unitary.**  It is a permutation matrix, so its
conjugate transpose is the permutation matrix of the inverse permutation
(`Matrix.conjTranspose_permMatrix`), and the two multiply to the identity
(`Matrix.permMatrix_mul`). -/
theorem toffoli_unitary : toffoli ∈ Matrix.unitaryGroup (Fin 8) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  show toffoli * toffoliᴴ = 1
  rw [toffoli, conjTranspose_permMatrix, ← permMatrix_mul, inv_mul_cancel, permMatrix_one]

/-- The Toffoli matrix is self-adjoint, so it also equals its own (matrix) inverse. -/
theorem toffoli_conjTranspose : toffoliᴴ = toffoli := by
  have : (Equiv.swap (6 : Fin 8) 7)⁻¹ = Equiv.swap 6 7 := Equiv.swap_inv 6 7
  rw [toffoli, conjTranspose_permMatrix, toffoliPerm, this]

end QC

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false


import Mathlib

/-!
# Cnot Unitary Involutive
Category: Quantum Computing
Target: QC.cnot_unitary_involutive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix

/-- The controlled-NOT (CNOT) gate as a `4 × 4` complex matrix, in the
computational basis ordering `|00⟩, |01⟩, |10⟩, |11⟩`.  It leaves the target
qubit alone when the control qubit is `|0⟩` and flips it when the control
qubit is `|1⟩`. -/
def cnot : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

/-- CNOT squares to the identity. -/
theorem cnot_mul_self : cnot * cnot = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cnot, Matrix.mul_apply, Fin.sum_univ_succ]

/-- CNOT is a real symmetric matrix, hence self-adjoint. -/
theorem cnot_conjTranspose : cnotᴴ = cnot := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cnot, Matrix.conjTranspose_apply]

/-- **CNOT is unitary and involutive.**

Explicitly: `cnotᴴ * cnot = 1` and `cnot * cnotᴴ = 1` (unitarity, stated both
as the two adjoint identities and as membership in the unitary group), and
`cnot * cnot = 1` (`CNOT² = I`, so CNOT is its own inverse). -/
theorem cnot_unitary_involutive :
    cnotᴴ * cnot = 1 ∧ cnot * cnotᴴ = 1 ∧
      cnot ∈ unitary (Matrix (Fin 4) (Fin 4) ℂ) ∧
      cnot * cnot = 1 := by
  refine ⟨?_, ?_, ⟨?_, ?_⟩, cnot_mul_self⟩ <;>
    first
      | (rw [show cnotᴴ = cnot from cnot_conjTranspose]; exact cnot_mul_self)
      | (rw [show star cnot = cnot from cnot_conjTranspose]; exact cnot_mul_self)

/-- CNOT belongs to the unitary group `U(4)`. -/
theorem cnot_mem_unitaryGroup : cnot ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
  cnot_unitary_involutive.2.2.1

end QC


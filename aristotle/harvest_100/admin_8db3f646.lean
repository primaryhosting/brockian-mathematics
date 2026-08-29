import Mathlib
/-!
# Density Matrix Unitary Invariant
Category: Quantum Computing
Target: QC.density_matrix_unitary_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Conjugating a matrix by a unitary preserves the trace:
`Tr (U ρ U†) = Tr ρ`, by cyclicity of the trace (`Matrix.trace_mul_comm`). -/
theorem trace_conj_unitary (U ρ : Matrix n n ℂ) (hU : Uᴴ * U = 1) :
    (U * ρ * Uᴴ).trace = ρ.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

/-- **Density matrices are preserved under unitary conjugation.**

If `ρ` is positive semidefinite with unit trace (a density matrix) and `U` is unitary,
then `U ρ U†` is again positive semidefinite with unit trace.

Positive semidefiniteness is exactly Mathlib's
`Matrix.PosSemidef.mul_mul_conjTranspose_same`, and the trace claim follows from
cyclicity of the trace (`Matrix.trace_mul_comm`) together with `Uᴴ * U = 1`. -/
theorem density_matrix_unitary_invariant
    (ρ U : Matrix n n ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    (U * ρ * Uᴴ).PosSemidef ∧ (U * ρ * Uᴴ).trace = 1 := by
  refine ⟨hρ.mul_mul_conjTranspose_same U, ?_⟩
  rw [trace_conj_unitary U ρ (Matrix.mem_unitaryGroup_iff'.mp hU), htr]

end QC


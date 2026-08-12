/-
# Density Matrix Unitary Invariant
Category: Quantum Computing
Target: QC.density_matrix_unitary_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Density Matrix Unitary Invariant
Category: Quantum Computing
Target: QC.density_matrix_unitary_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

open scoped Matrix ComplexOrder

namespace QC

/-- **Unitary invariance of density matrices.**
If `ρ` is a density matrix (positive semidefinite with unit trace) and `U` is unitary
(`Uᴴ * U = 1`), then the conjugated matrix `U * ρ * Uᴴ` is again a density matrix.

The positivity part is `Matrix.PosSemidef.mul_mul_conjTranspose_same` from Mathlib;
the trace part follows from cyclicity of the trace (`Matrix.trace_mul_comm`). -/
theorem density_matrix_unitary_invariant {n : Type*} [Fintype n] [DecidableEq n]
    (ρ U : Matrix n n ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hU : Uᴴ * U = 1) :
    (U * ρ * Uᴴ).PosSemidef ∧ (U * ρ * Uᴴ).trace = 1 := by
  refine ⟨hρ.mul_mul_conjTranspose_same U, ?_⟩
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul, htr]

/-- Version of `QC.density_matrix_unitary_invariant` phrased with membership in the
unitary group `Matrix.unitaryGroup n ℂ`. -/
theorem density_matrix_unitaryGroup_invariant {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : Matrix n n ℂ) (U : Matrix.unitaryGroup n ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    ((U : Matrix n n ℂ) * ρ * (U : Matrix n n ℂ)ᴴ).PosSemidef ∧
      ((U : Matrix n n ℂ) * ρ * (U : Matrix n n ℂ)ᴴ).trace = 1 :=
  density_matrix_unitary_invariant ρ (U : Matrix n n ℂ) hρ htr
    (Matrix.UnitaryGroup.star_mul_self U)

end QC


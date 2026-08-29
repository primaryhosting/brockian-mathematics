/-
# Density Matrix Unitary Invariant
Category: Quantum Computing
Target: QC.density_matrix_unitary_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QC

open Matrix
open scoped ComplexOrder

/-- Conjugating a matrix by a unitary preserves the trace. -/
theorem trace_unitary_conj {n : Type*} [Fintype n] [DecidableEq n]
    (U ρ : Matrix n n ℂ) (hU : Uᴴ * U = 1) :
    trace (U * ρ * Uᴴ) = trace ρ := by
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]

/-- **Density matrix unitary invariance.**
If `ρ` is a density matrix (positive semidefinite with unit trace) and `U` is unitary,
then `U * ρ * Uᴴ` is again a density matrix. -/
theorem density_matrix_unitary_invariant {n : Type*} [Fintype n] [DecidableEq n]
    (U ρ : Matrix n n ℂ) (hU : Uᴴ * U = 1) (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    (U * ρ * Uᴴ).PosSemidef ∧ trace (U * ρ * Uᴴ) = 1 :=
  ⟨hρ.mul_mul_conjTranspose_same U, by rw [trace_unitary_conj U ρ hU, htr]⟩

end QC


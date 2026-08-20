/-
# Density Matrix Unitary Invariant
Category: Quantum Computing
Target: QC.density_matrix_unitary_invariant
Verification: verified
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

/-- **Unitary invariance of density matrices.**
If `ρ` is positive semidefinite with unit trace (a density matrix) and `U` is unitary
(a member of the unitary group, i.e. `Uᴴ * U = U * Uᴴ = 1`), then the conjugated
matrix `U * ρ * Uᴴ` is again a density matrix: it is positive semidefinite and has unit trace. -/
theorem density_matrix_unitary_invariant
    {n : Type*} [Fintype n] [DecidableEq n]
    (ρ U : Matrix n n ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    (U * ρ * Uᴴ).PosSemidef ∧ (U * ρ * Uᴴ).trace = 1 := by
  have hU' : Uᴴ * U = 1 := hU.1
  refine ⟨hρ.mul_mul_conjTranspose_same U, ?_⟩
  rw [Matrix.trace_mul_cycle, hU', Matrix.one_mul, htr]

end QC


/-!
# Density Matrix Unitary Invariant
Category: Quantum Computing
Target: QC.density_matrix_unitary_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Unitary invariance of density matrices.**

If `ρ` is a density matrix (positive semidefinite with unit trace) and `U` is unitary
(`U * Uᴴ = 1` and `Uᴴ * U = 1`), then `U * ρ * Uᴴ` is again a density matrix:
it is positive semidefinite and has unit trace. -/
theorem density_matrix_unitary_invariant
    (ρ U : Matrix n n ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hU : U * Uᴴ = 1) (hU' : Uᴴ * U = 1) :
    (U * ρ * Uᴴ).PosSemidef ∧ (U * ρ * Uᴴ).trace = 1 := by
  refine ⟨hρ.mul_mul_conjTranspose_same U, ?_⟩
  rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hU', Matrix.one_mul, htr]

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


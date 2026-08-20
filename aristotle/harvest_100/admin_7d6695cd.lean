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
open scoped ComplexOrder
open Matrix

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

namespace QC

/-- A density matrix: positive semidefinite with unit trace. -/
structure IsDensityMatrix {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : Matrix n n ℂ) : Prop where
  posSemidef : ρ.PosSemidef
  trace_one : ρ.trace = 1

/-- **Unitary invariance of density matrices.**
If `ρ` is positive semidefinite with unit trace and `U` is unitary, then `U ρ U†`
is again positive semidefinite with unit trace. -/
theorem density_matrix_unitary_invariant {n : Type*} [Fintype n] [DecidableEq n]
    (ρ U : Matrix n n ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    (U * ρ * Uᴴ).PosSemidef ∧ (U * ρ * Uᴴ).trace = 1 := by
  refine ⟨hρ.mul_mul_conjTranspose_same U, ?_⟩
  have hUU : Uᴴ * U = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Unitary.star_mul_self_of_mem hU)
  calc (U * ρ * Uᴴ).trace = (Uᴴ * (U * ρ)).trace := by
        rw [Matrix.trace_mul_comm]
    _ = ρ.trace := by rw [← Matrix.mul_assoc, hUU, Matrix.one_mul]
    _ = 1 := htr

/-- Packaged form: the conjugation of a density matrix by a unitary is a density matrix. -/
theorem isDensityMatrix_conj {n : Type*} [Fintype n] [DecidableEq n]
    (ρ U : Matrix n n ℂ) (hρ : IsDensityMatrix ρ) (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    IsDensityMatrix (U * ρ * Uᴴ) :=
  let h := density_matrix_unitary_invariant ρ U hρ.posSemidef hρ.trace_one hU
  ⟨h.1, h.2⟩

end QC

#print axioms QC.density_matrix_unitary_invariant
#print axioms QC.isDensityMatrix_conj


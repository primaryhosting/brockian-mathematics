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

open scoped ComplexOrder

namespace QC

open Matrix

/-- **Unitary invariance of density matrices.**
If `ρ` is positive semidefinite with `Tr ρ = 1` and `U` is unitary, then `U ρ U†` is
positive semidefinite and `Tr (U ρ U†) = 1`. -/
theorem density_matrix_unitary_invariant {n : Type*} [Fintype n] [DecidableEq n]
    (ρ U : Matrix n n ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    (U * ρ * Uᴴ).PosSemidef ∧ (U * ρ * Uᴴ).trace = 1 := by
  have h : Uᴴ * U = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff' (A := U)).mp hU
  refine ⟨hρ.mul_mul_conjTranspose_same U, ?_⟩
  rw [Matrix.trace_mul_cycle, h, Matrix.one_mul, htr]

end QC


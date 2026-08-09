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

namespace QC

/-- The 3-qubit GHZ state `(|000⟩ + |111⟩)/√2`, as a vector in the Hilbert space
`EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2)` of three qubits. -/
noncomputable def ghz3 : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2) :=
  ((Real.sqrt 2 : ℂ))⁻¹ •
    (EuclideanSpace.single (0, 0, 0) 1 + EuclideanSpace.single (1, 1, 1) 1)

/-- The amplitudes of the GHZ state: `1/√2` on `|000⟩` and `|111⟩`, and `0` elsewhere. -/
theorem ghz3_apply (i : Fin 2 × Fin 2 × Fin 2) :
    ghz3 i = if i = (0, 0, 0) ∨ i = (1, 1, 1) then ((Real.sqrt 2 : ℂ))⁻¹ else 0 := by
  fin_cases i <;> simp [ghz3, EuclideanSpace.single_apply, Prod.ext_iff]

/-- The 3-qubit GHZ state `(|000⟩ + |111⟩)/√2` is a unit vector. -/
theorem ghz3_normalized : ‖ghz3‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [ghz3, PiLp.smul_apply, PiLp.add_apply, EuclideanSpace.single_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Prod.ext_iff, smul_eq_mul]
  norm_num

end QC


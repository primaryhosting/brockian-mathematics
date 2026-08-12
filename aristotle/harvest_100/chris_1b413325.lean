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

/-- The computational basis state `|i⟩` of a two-qubit system, where the state space is
the complex Hilbert space `EuclideanSpace ℂ (Fin 2 × Fin 2)` with basis indexed by pairs of
bits. -/
noncomputable def ket (i : Fin 2 × Fin 2) : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  EuclideanSpace.single i 1

/-- The two-qubit GHZ (Bell) state `(|00⟩ + |11⟩)/√2`. -/
noncomputable def ghz2 : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (ket (0, 0) + ket (1, 1))

/-- The two-qubit GHZ state `(|00⟩ + |11⟩)/√2` is a unit vector. -/
theorem ghz2_normalized : ‖ghz2‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [ghz2, ket, Fintype.sum_prod_type, Fin.sum_univ_succ, EuclideanSpace.single_apply]
  norm_num

end QC


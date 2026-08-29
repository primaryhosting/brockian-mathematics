/-
# Ghz 2 Normalized
Category: Quantum Computing
Target: QC.ghz2_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The 2-qubit GHZ state `(|00⟩ + |11⟩)/√2`, as a vector in the Hilbert space
`EuclideanSpace ℂ (Fin 2 × Fin 2)` whose standard basis vectors are the
computational basis states `|ij⟩`. -/
noncomputable def ghz2 : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  ((Real.sqrt 2)⁻¹ : ℝ) •
    (EuclideanSpace.single (0, 0) (1 : ℂ) + EuclideanSpace.single (1, 1) (1 : ℂ))

/-- The 2-qubit GHZ state is a unit vector. -/
theorem ghz2_normalized : ‖ghz2‖ = 1 := by
  simp [ghz2, EuclideanSpace.norm_eq, Fintype.sum_prod_type, Fin.sum_univ_two,
    EuclideanSpace.single_apply, Prod.ext_iff]
  norm_num

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


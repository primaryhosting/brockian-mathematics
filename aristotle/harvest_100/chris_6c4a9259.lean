import Mathlib
/-!
# Ghz 3 Normalized
Category: Quantum Computing
Target: QC.ghz3_normalized
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

/-- The three-qubit GHZ state `(|000⟩ + |111⟩)/√2`, as a vector in the
Hilbert space `EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2)`. -/
noncomputable def ghz3 : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2) :=
  WithLp.toLp 2
    (fun v => if v = (0, 0, 0) ∨ v = (1, 1, 1) then (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0)

/-- `ghz3` really is `(|000⟩ + |111⟩)/√2`, expressed via the standard basis vectors
`EuclideanSpace.single`. -/
theorem ghz3_eq : ghz3 = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
    (EuclideanSpace.single ((0, 0, 0) : Fin 2 × Fin 2 × Fin 2) (1 : ℂ)
      + EuclideanSpace.single ((1, 1, 1) : Fin 2 × Fin 2 × Fin 2) (1 : ℂ)) := by
  ext v
  by_cases h1 : v = (0, 0, 0) <;> by_cases h2 : v = (1, 1, 1) <;>
    simp [ghz3, EuclideanSpace.single_apply, h1, h2]

/-- The 3-qubit GHZ state is a unit vector. -/
theorem ghz3_normalized : ‖ghz3‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [ghz3, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num

end QC

#print axioms QC.ghz3_normalized


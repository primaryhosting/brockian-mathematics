import Mathlib
/-!
# Ghz 3 Normalized
Category: Quantum Computing
Target: QC.ghz3_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The 3-qubit GHZ state `(|000⟩ + |111⟩)/√2`, as a vector in the Hilbert space
`EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2)` of three qubits. -/
noncomputable def ghz3 : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2) :=
  WithLp.toLp 2 fun q => if q = (0, 0, 0) ∨ q = (1, 1, 1) then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0

/-- `ghz3` is indeed `(|000⟩ + |111⟩)/√2`, written with the standard basis vectors. -/
theorem ghz3_eq_smul_add_single : ghz3 = (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) •
    (EuclideanSpace.single ((0, 0, 0) : Fin 2 × Fin 2 × Fin 2) (1 : ℂ)
      + EuclideanSpace.single ((1, 1, 1) : Fin 2 × Fin 2 × Fin 2) (1 : ℂ)) := by
  ext q
  simp [ghz3, EuclideanSpace.single_apply]
  by_cases h1 : q = (0, 0, 0) <;> by_cases h2 : q = (1, 1, 1) <;> simp [h1, h2]

/-- The 3-qubit GHZ state is a unit vector. -/
theorem ghz3_normalized : ‖ghz3‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [ghz3, Fintype.sum_prod_type, Fin.sum_univ_two, WithLp.ofLp_toLp]
  norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]

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


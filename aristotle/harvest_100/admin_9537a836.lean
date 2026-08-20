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
  fun p => if p = (0, 0, 0) ∨ p = (1, 1, 1) then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0

/-- The 3-qubit GHZ state is a unit vector. -/
theorem ghz3_normalized : ‖ghz3‖ = 1 := by
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ p : Fin 2 × Fin 2 × Fin 2, ‖ghz3 p‖ ^ 2 = 1 := by
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, ghz3]
    norm_num
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_pow, hsq]
    norm_num
  rw [hsum, Real.sqrt_one]

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


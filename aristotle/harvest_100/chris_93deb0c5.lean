import Mathlib

/-!
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- Computational-basis index type for 4 qubits: bit strings `(b₀, b₁, b₂, b₃)`. -/
abbrev Qubits4 := Fin 2 × Fin 2 × Fin 2 × Fin 2

/-- The all-zeros basis state `|0000⟩`. -/
noncomputable def ket0000 : EuclideanSpace ℂ Qubits4 :=
  EuclideanSpace.single (0, 0, 0, 0) 1

/-- The all-ones basis state `|1111⟩`. -/
noncomputable def ket1111 : EuclideanSpace ℂ Qubits4 :=
  EuclideanSpace.single (1, 1, 1, 1) 1

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2`. -/
noncomputable def ghz4 : EuclideanSpace ℂ Qubits4 :=
  ((Real.sqrt 2 : ℝ)⁻¹ : ℂ) • (ket0000 + ket1111)

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2` is a unit vector. -/
theorem ghz4_normalized : ‖ghz4‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [ghz4, ket0000, ket1111, EuclideanSpace.single_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Prod.ext_iff]
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


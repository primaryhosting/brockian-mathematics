import Mathlib
/-!
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The computational basis of a 4-qubit system, indexed by four bits. -/
abbrev Qubits4 := Fin 2 × Fin 2 × Fin 2 × Fin 2

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2`, as a vector in the
Hilbert space `ℂ^16` of four qubits. -/
noncomputable def ghz4 : EuclideanSpace ℂ Qubits4 :=
  WithLp.toLp 2 (fun i =>
    if i = (0, 0, 0, 0) then ((1 / Real.sqrt 2 : ℝ) : ℂ)
    else if i = (1, 1, 1, 1) then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0)

/-- The 4-qubit GHZ state is a unit vector. -/
theorem ghz4_normalized : ‖ghz4‖ = 1 := by
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i : Qubits4, ‖ghz4.ofLp i‖ ^ 2 = 1 := by
    simp only [ghz4, WithLp.ofLp_toLp, Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num [Complex.norm_real, div_pow, hsq]
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


/-
# Ghz 7 Normalized
Category: Quantum Computing
Target: QC.ghz7_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The computational basis of a 7-qubit register is indexed by bit strings
`Fin 7 → Bool`; states live in the Hilbert space `EuclideanSpace ℂ (Fin 7 → Bool)`. -/
abbrev Qubits7 := EuclideanSpace ℂ (Fin 7 → Bool)

/-- The all-zeros basis state `|0000000⟩`. -/
noncomputable def allZeros : Qubits7 := EuclideanSpace.single (fun _ => false) 1

/-- The all-ones basis state `|1111111⟩`. -/
noncomputable def allOnes : Qubits7 := EuclideanSpace.single (fun _ => true) 1

/-- The 7-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2`. -/
noncomputable def ghz7 : Qubits7 := (Real.sqrt 2)⁻¹ • (allZeros + allOnes)

private lemma inner_allZeros_allOnes : (inner ℂ allZeros allOnes : ℂ) = 0 := by
  simp [allZeros, allOnes, EuclideanSpace.inner_single_left,
    EuclideanSpace.single_apply, funext_iff]

private lemma norm_allZeros_add_allOnes : ‖allZeros + allOnes‖ = Real.sqrt 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)
    allZeros allOnes inner_allZeros_allOnes
  have h1 : ‖allZeros‖ = 1 := by simp [allZeros]
  have h2 : ‖allOnes‖ = 1 := by simp [allOnes]
  rw [h1, h2] at h
  have hnn : (0:ℝ) ≤ ‖allZeros + allOnes‖ := norm_nonneg _
  have : ‖allZeros + allOnes‖ ^ 2 = 2 := by nlinarith
  rw [← this, Real.sqrt_sq hnn]

/-- The 7-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2` is a unit vector. -/
theorem ghz7_normalized : ‖ghz7‖ = 1 := by
  rw [ghz7, norm_smul, norm_allZeros_add_allOnes]
  simp [abs_of_nonneg (Real.sqrt_nonneg 2)]

end QC

#print axioms QC.ghz7_normalized

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


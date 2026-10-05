/-
# Ghz 7 Normalized
Category: Quantum Computing
Target: QC.ghz7_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The state space of 7 qubits: the complex Hilbert space with orthonormal basis
indexed by the computational basis states `Fin 7 → Bool`. -/
abbrev Qubits7 := EuclideanSpace ℂ (Fin 7 → Bool)

/-- The computational basis state `|b⟩` for a bit string `b : Fin 7 → Bool`. -/
noncomputable def basisState (b : Fin 7 → Bool) : Qubits7 := EuclideanSpace.single b 1

/-- The all-zeros basis state `|0000000⟩`. -/
noncomputable def allZeros : Qubits7 := basisState (fun _ => false)

/-- The all-ones basis state `|1111111⟩`. -/
noncomputable def allOnes : Qubits7 := basisState (fun _ => true)

/-- The 7-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2`. -/
noncomputable def ghz7 : Qubits7 := (Real.sqrt 2 : ℂ)⁻¹ • (allZeros + allOnes)

/-- The components of the GHZ state: it is `1/√2` on the all-zeros and all-ones
basis vectors, and `0` elsewhere. -/
theorem ghz7_apply (v : Fin 7 → Bool) :
    ghz7 v = if (∀ i, v i = false) ∨ (∀ i, v i = true) then ((Real.sqrt 2 : ℂ)⁻¹) else 0 := by
  have hne : (fun _ : Fin 7 => false) ≠ (fun _ : Fin 7 => true) := by
    intro h; simpa using congrFun h 0
  by_cases h0 : ∀ i, v i = false
  · have hv : v = fun _ => false := funext h0
    subst hv
    simp [ghz7, allZeros, allOnes, basisState, EuclideanSpace.single_apply]
    exact hne
  · by_cases h1 : ∀ i, v i = true
    · have hv : v = fun _ => true := funext h1
      subst hv
      simp [ghz7, allZeros, allOnes, basisState, EuclideanSpace.single_apply]
      exact hne.symm
    · have e0 : v ≠ fun _ => false := fun h => h0 (fun i => by rw [h])
      have e1 : v ≠ fun _ => true := fun h => h1 (fun i => by rw [h])
      simp [ghz7, allZeros, allOnes, basisState, EuclideanSpace.single_apply,
        h0, h1, e0, e1]

/-- The 7-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2` is a unit vector. -/
theorem ghz7_normalized : ‖ghz7‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have h : ∀ v : Fin 7 → Bool, ‖ghz7 v‖ ^ 2 =
      if (∀ i, v i = false) ∨ (∀ i, v i = true) then (1 / 2 : ℝ) else 0 := by
    intro v
    by_cases hv : (∀ i, v i = false) ∨ (∀ i, v i = true) <;>
      simp [ghz7_apply, hv, Real.sq_sqrt]
  simp only [h]
  rw [← Finset.sum_filter]
  have hc : (Finset.univ.filter
      (fun v : Fin 7 → Bool => (∀ i, v i = false) ∨ (∀ i, v i = true))).card = 2 := by decide
  rw [Finset.sum_const, hc]
  norm_num

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


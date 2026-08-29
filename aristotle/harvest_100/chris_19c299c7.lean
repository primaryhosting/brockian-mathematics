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
`Fin 7 → Bool`; the state space is the Hilbert space `EuclideanSpace ℂ (Fin 7 → Bool)`. -/
abbrev Qubits7 := EuclideanSpace ℂ (Fin 7 → Bool)

/-- The all-zeros bit string `|0…0⟩`. -/
def allZeros : Fin 7 → Bool := fun _ => false

/-- The all-ones bit string `|1…1⟩`. -/
def allOnes : Fin 7 → Bool := fun _ => true

/-- The 7-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2`. -/
noncomputable def ghz7 : Qubits7 :=
  ((1 : ℂ) / (Real.sqrt 2 : ℝ)) •
    (EuclideanSpace.single allZeros 1 + EuclideanSpace.single allOnes 1)

/-- The 7-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2` is a unit vector. -/
theorem ghz7_normalized : ‖ghz7‖ = 1 := by
  have hne : allZeros ≠ allOnes := by
    intro h; have := congrFun h 0; simp [allZeros, allOnes] at this
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [EuclideanSpace.norm_eq]
  have hval : ∀ x : Fin 7 → Bool, ‖ghz7.ofLp x‖ ^ 2 =
      (if x = allZeros then (1 / 2 : ℝ) else 0)
        + (if x = allOnes then (1 / 2 : ℝ) else 0) := by
    intro x
    simp only [ghz7, PiLp.smul_apply, PiLp.add_apply, EuclideanSpace.single_apply, smul_eq_mul]
    by_cases h0 : x = allZeros <;> by_cases h1 : x = allOnes <;>
      simp [h0, h1, hne, hne.symm, hsq]
  rw [Finset.sum_congr rfl (fun x _ => hval x), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ allZeros (fun _ => (1 / 2 : ℝ)),
    Finset.sum_ite_eq' Finset.univ allOnes (fun _ => (1 / 2 : ℝ))]
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


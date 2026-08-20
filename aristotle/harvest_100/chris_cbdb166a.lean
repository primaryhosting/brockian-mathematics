/-
# Ghz 8 Normalized
Category: Quantum Computing
Target: QC.ghz8_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ghz 8 Normalized
Category: Quantum Computing
Target: QC.ghz8_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The computational basis of an 8-qubit system is indexed by bit strings
`Fin 8 → Bool`; the state space is the Hilbert space `EuclideanSpace ℂ (Fin 8 → Bool)`. -/
abbrev Qubits8 := EuclideanSpace ℂ (Fin 8 → Bool)

/-- The all-zeros bit string `|0…0⟩`. -/
def allZeros : Fin 8 → Bool := fun _ => false

/-- The all-ones bit string `|1…1⟩`. -/
def allOnes : Fin 8 → Bool := fun _ => true

theorem allZeros_ne_allOnes : allZeros ≠ allOnes := by
  intro h
  have := congrFun h 0
  simp [allZeros, allOnes] at this

/-- The 8-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2`, written out in coordinates. -/
noncomputable def ghz8 : Qubits8 :=
  WithLp.toLp 2 (fun b =>
    if b = allZeros then ((1 / Real.sqrt 2 : ℝ) : ℂ)
    else if b = allOnes then ((1 / Real.sqrt 2 : ℝ) : ℂ)
    else 0)

/-- `ghz8` is indeed `(1/√2) • (|0…0⟩ + |1…1⟩)` in terms of basis vectors. -/
theorem ghz8_eq_smul_add_single :
    ghz8 = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
      (EuclideanSpace.single allZeros (1 : ℂ) + EuclideanSpace.single allOnes (1 : ℂ)) := by
  ext b
  by_cases h0 : b = allZeros
  · subst h0
    simp [ghz8, EuclideanSpace.single_apply, allZeros_ne_allOnes]
  · by_cases h1 : b = allOnes
    · subst h1
      simp [ghz8, EuclideanSpace.single_apply, h0]
    · simp [ghz8, EuclideanSpace.single_apply, h0, h1]

/-- **The 8-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2` is a unit vector.** -/
theorem ghz8_normalized : ‖ghz8‖ = 1 := by
  have hne : allZeros ≠ allOnes := allZeros_ne_allOnes
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [EuclideanSpace.norm_eq]
  have h : ∀ b : Fin 8 → Bool, ‖ghz8 b‖ ^ 2 =
      (if b = allZeros then (1 / 2 : ℝ) else 0) + (if b = allOnes then (1 / 2 : ℝ) else 0) := by
    intro b
    by_cases h0 : b = allZeros
    · subst h0
      simp [ghz8, hne, h2]
    · by_cases h1 : b = allOnes
      · subst h1
        simp [ghz8, Ne.symm hne, h2]
      · simp [ghz8, h0, h1]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ]
  norm_num

end QC

#print axioms QC.ghz8_normalized

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


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

namespace QC

/-- The all-zeros bit string of length 8, labelling the basis state `|0…0⟩`. -/
def allZeros : Fin 8 → Bool := fun _ => false

/-- The all-ones bit string of length 8, labelling the basis state `|1…1⟩`. -/
def allOnes : Fin 8 → Bool := fun _ => true

lemma allZeros_ne_allOnes : allZeros ≠ allOnes := by
  intro h
  have := congrFun h 0
  simp [allZeros, allOnes] at this

/-- The 8-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2`, as a vector in the `2^8`-dimensional
complex Hilbert space `EuclideanSpace ℂ (Fin 8 → Bool)` whose basis states are indexed
by the bit strings of length 8. -/
noncomputable def ghz8 : EuclideanSpace ℂ (Fin 8 → Bool) :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) •
    (EuclideanSpace.single allZeros (1 : ℂ) + EuclideanSpace.single allOnes (1 : ℂ))

/-- The coordinates of the GHZ state: `1/√2` at `|0…0⟩` and `|1…1⟩`, zero elsewhere. -/
lemma ghz8_apply (b : Fin 8 → Bool) :
    ghz8.ofLp b = if b = allZeros ∨ b = allOnes then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0 := by
  by_cases h0 : b = allZeros
  · simp [ghz8, h0, EuclideanSpace.single_apply, allZeros_ne_allOnes]
  · by_cases h1 : b = allOnes
    · simp [ghz8, h1, EuclideanSpace.single_apply, allZeros_ne_allOnes.symm]
    · simp [ghz8, h0, h1, EuclideanSpace.single_apply]

/-- Squared modulus of each coordinate of the GHZ state, split as a sum of two
indicator terms. -/
lemma ghz8_normSq_apply (b : Fin 8 → Bool) :
    ‖ghz8.ofLp b‖ ^ 2 = (if b = allZeros then (1 / 2 : ℝ) else 0)
      + (if b = allOnes then (1 / 2 : ℝ) else 0) := by
  rw [ghz8_apply]
  by_cases h0 : b = allZeros
  · simp [h0, allZeros_ne_allOnes]
  · by_cases h1 : b = allOnes
    · simp [h1, allZeros_ne_allOnes.symm]
    · simp [h0, h1]

/-- The 8-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2` is a unit vector. -/
theorem ghz8_normalized : ‖ghz8‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have h : ∑ b : Fin 8 → Bool, ‖ghz8.ofLp b‖ ^ 2 = 1 := by
    simp only [ghz8_normSq_apply]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ allZeros
      (fun _ => (1 / 2 : ℝ)), Finset.sum_ite_eq' Finset.univ allOnes
      (fun _ => (1 / 2 : ℝ))]
    norm_num
  rw [h, Real.sqrt_one]

end QC


/-
# Ghz 8 Normalized
Category: Quantum Computing
Target: QC.ghz8_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open EuclideanSpace

/-- The all-zeros basis state index `|00000000⟩` of an 8-qubit register,
represented as the constant `false` function on `Fin 8`. -/
def allZeros : Fin 8 → Bool := fun _ => false

/-- The all-ones basis state index `|11111111⟩` of an 8-qubit register,
represented as the constant `true` function on `Fin 8`. -/
def allOnes : Fin 8 → Bool := fun _ => true

/-- The 8-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2`, as a vector in the
`2^8`-dimensional complex Hilbert space `EuclideanSpace ℂ (Fin 8 → Bool)`. -/
noncomputable def ghz8 : EuclideanSpace ℂ (Fin 8 → Bool) :=
  (Real.sqrt 2)⁻¹ • (EuclideanSpace.single allZeros 1 + EuclideanSpace.single allOnes 1)

lemma allZeros_ne_allOnes : allZeros ≠ allOnes := by
  intro h
  have := congrFun h 0
  simp [allZeros, allOnes] at this

/-- The two computational basis states occurring in the GHZ state are orthogonal. -/
lemma inner_single_allZeros_allOnes :
    inner ℂ (EuclideanSpace.single allZeros (1 : ℂ))
      (EuclideanSpace.single allOnes (1 : ℂ)) = 0 := by
  rw [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  simp [allZeros_ne_allOnes]

/-- The unnormalized GHZ vector `|0…0⟩ + |1…1⟩` has norm `√2`. -/
lemma norm_ghz8_unnormalized :
    ‖(EuclideanSpace.single allZeros (1 : ℂ) + EuclideanSpace.single allOnes (1 : ℂ))‖
      = Real.sqrt 2 := by
  have hsq := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
    inner_single_allZeros_allOnes
  rw [EuclideanSpace.norm_single, EuclideanSpace.norm_single] at hsq
  have h2 : ‖(EuclideanSpace.single allZeros (1 : ℂ)
      + EuclideanSpace.single allOnes (1 : ℂ))‖ ^ 2 = 2 := by
    rw [pow_two, hsq]; norm_num
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2,
    norm_nonneg (EuclideanSpace.single allZeros (1 : ℂ)
      + EuclideanSpace.single allOnes (1 : ℂ))]

/-- **The 8-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2` is a unit vector.** -/
theorem ghz8_normalized : ‖ghz8‖ = 1 := by
  rw [ghz8, norm_smul, norm_ghz8_unnormalized]
  simp [abs_of_nonneg (Real.sqrt_nonneg 2)]

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


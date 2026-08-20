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

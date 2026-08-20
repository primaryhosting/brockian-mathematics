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

lemma inner_single_allZeros_allOnes :
    inner ℂ (EuclideanSpace.single allZeros (1 : ℂ))
      (EuclideanSpace.single allOnes (1 : ℂ)) = 0 := by
  rw [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  simp [allZeros_ne_allOnes]

/-- The unnormalized GHZ vector `|0…0⟩ + |1…1⟩` has norm `√2`. -/

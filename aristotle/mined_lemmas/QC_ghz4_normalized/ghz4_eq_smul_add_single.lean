/-
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The all-zeros computational basis label `|0000⟩` for four qubits. -/

lemma ghz4_eq_smul_add_single :
    ghz4 = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
      (EuclideanSpace.single allZeros (1 : ℂ) + EuclideanSpace.single allOnes (1 : ℂ)) := by
  ext x
  by_cases h0 : x = allZeros
  · subst h0
    simp [ghz4, EuclideanSpace.single_apply, allZeros_ne_allOnes]
  · by_cases h1 : x = allOnes
    · subst h1
      simp [ghz4, EuclideanSpace.single_apply, h0]
    · simp [ghz4, EuclideanSpace.single_apply, h0, h1]

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2` is a unit vector. -/

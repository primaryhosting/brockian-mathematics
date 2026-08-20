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

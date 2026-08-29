/-!
# Ghz 5 Normalized
Category: Quantum Computing
Target: QC.ghz5_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- Computational basis labels for 5 qubits: functions `Fin 5 → Bool`
(so the state space `EuclideanSpace ℂ (Fin 5 → Bool)` is the 32-dimensional
tensor product of five qubit spaces). -/
abbrev Qubits5 := Fin 5 → Bool

/-- The all-zeros label `|00000⟩`. -/

theorem ghz5_eq_smul_add_single :
    ghz5 = (1 / Real.sqrt 2 : ℝ) •
      (EuclideanSpace.single allZero (1 : ℂ) + EuclideanSpace.single allOne (1 : ℂ)) := by
  ext v
  by_cases h1 : v = allZero
  · subst h1
    simp [ghz5, EuclideanSpace.single_apply, Ne.symm allZero_ne_allOne]
  · by_cases h2 : v = allOne
    · subst h2
      simp [ghz5, EuclideanSpace.single_apply, allZero_ne_allOne]
    · simp [ghz5, EuclideanSpace.single_apply, h1, h2, Ne.symm h1, Ne.symm h2]

/-- **The 5-qubit GHZ state is a unit vector.** -/

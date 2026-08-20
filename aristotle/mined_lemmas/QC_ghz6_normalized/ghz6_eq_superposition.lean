import Mathlib

/-!
# Ghz 6 Normalized
Category: Quantum Computing
Target: QC.ghz6_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- Computational basis states of 6 qubits, indexed by bit strings `Fin 6 → Bool`. -/
abbrev Qubits6 := Fin 6 → Bool

/-- The 6-qubit GHZ state `(|000000⟩ + |111111⟩)/√2`, as a vector in the
Hilbert space `EuclideanSpace ℂ (Fin 6 → Bool)`. -/

theorem ghz6_eq_superposition :
    ghz6 = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
      (EuclideanSpace.single (fun _ => false) (1 : ℂ)
        + EuclideanSpace.single (fun _ => true) (1 : ℂ)) := by
  have hne := allFalse_ne_allTrue
  ext b
  by_cases h1 : b = (fun _ => false)
  · simp [ghz6, h1, EuclideanSpace.single_apply, hne]
  · by_cases h2 : b = (fun _ => true)
    · simp [ghz6, h2, EuclideanSpace.single_apply, hne.symm]
    · simp [ghz6, h1, h2, EuclideanSpace.single_apply]

/-- The 6-qubit GHZ state is a unit vector. -/

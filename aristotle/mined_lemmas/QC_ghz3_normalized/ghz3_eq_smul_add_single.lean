import Mathlib
/-!
# Ghz 3 Normalized
Category: Quantum Computing
Target: QC.ghz3_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The 3-qubit GHZ state `(|000⟩ + |111⟩)/√2`, as a vector in the Hilbert space
`EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2)` of three qubits. -/

theorem ghz3_eq_smul_add_single : ghz3 = (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) •
    (EuclideanSpace.single ((0, 0, 0) : Fin 2 × Fin 2 × Fin 2) (1 : ℂ)
      + EuclideanSpace.single ((1, 1, 1) : Fin 2 × Fin 2 × Fin 2) (1 : ℂ)) := by
  ext q
  simp [ghz3, EuclideanSpace.single_apply]
  by_cases h1 : q = (0, 0, 0) <;> by_cases h2 : q = (1, 1, 1) <;> simp [h1, h2]

/-- The 3-qubit GHZ state is a unit vector. -/

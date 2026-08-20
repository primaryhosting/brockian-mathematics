/-
# Ghz 7 Normalized
Category: Quantum Computing
Target: QC.ghz7_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The computational basis of a 7-qubit register is indexed by bit strings
`Fin 7 → Bool`; states live in the Hilbert space `EuclideanSpace ℂ (Fin 7 → Bool)`. -/
abbrev Qubits7 := EuclideanSpace ℂ (Fin 7 → Bool)

/-- The all-zeros basis state `|0000000⟩`. -/

private lemma norm_allZeros_add_allOnes : ‖allZeros + allOnes‖ = Real.sqrt 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)
    allZeros allOnes inner_allZeros_allOnes
  have h1 : ‖allZeros‖ = 1 := by simp [allZeros]
  have h2 : ‖allOnes‖ = 1 := by simp [allOnes]
  rw [h1, h2] at h
  have hnn : (0:ℝ) ≤ ‖allZeros + allOnes‖ := norm_nonneg _
  have : ‖allZeros + allOnes‖ ^ 2 = 2 := by nlinarith
  rw [← this, Real.sqrt_sq hnn]

/-- The 7-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2` is a unit vector. -/

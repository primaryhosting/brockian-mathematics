/-
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Matrix

namespace QC

/-! ## The quantum side: the GHZ state and its Pauli eigenvalue relations -/

/-- Index type for a three-qubit computational basis. -/
abbrev Idx := Fin 2 × Fin 2 × Fin 2

/-- The Pauli `X` observable. -/

theorem ghz_eigen_XYY : tensor3 pauliX pauliY pauliY *ᵥ ghz = ghz := by
  funext i
  obtain ⟨a, b, c⟩ := i
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ,
      tensor3, pauliX, pauliY, ghz]

/-- Quantum prediction: `Y ⊗ X ⊗ Y` has the GHZ state as a `+1` eigenvector. -/

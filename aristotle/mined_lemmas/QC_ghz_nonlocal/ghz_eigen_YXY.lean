/- (Lean requires `import` to precede any module docstring, so this required header is
   reproduced verbatim as a plain block comment.)
/-!
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

namespace QC

/-- Index type for the computational basis of three qubits. -/
abbrev Q3 := Fin 2 × Fin 2 × Fin 2

/-- The Pauli `X` matrix. -/

lemma ghz_eigen_YXY : Matrix.mulVec (op3 pauliY pauliX pauliY) ghz = -ghz := by
  funext p
  obtain ⟨a, b, c⟩ := p
  rw [mulVec_ghz]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [op3, ghz, pauliX, pauliY]

/-- `Y ⊗ Y ⊗ X` has the GHZ state as an eigenvector with eigenvalue `-1`. -/

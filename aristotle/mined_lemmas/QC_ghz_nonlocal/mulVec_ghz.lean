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

lemma mulVec_ghz (M : Matrix Q3 Q3 ℂ) (p : Q3) :
    Matrix.mulVec M ghz p = ((Real.sqrt 2)⁻¹ : ℝ) * (M p (0, 0, 0) + M p (1, 1, 1)) := by
  simp [Matrix.mulVec, dotProduct, ghz, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- `X ⊗ Y ⊗ Y` has the GHZ state as an eigenvector with eigenvalue `-1`. -/

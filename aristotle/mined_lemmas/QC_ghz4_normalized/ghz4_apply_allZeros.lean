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

lemma ghz4_apply_allZeros : ghz4.ofLp allZeros = ((Real.sqrt 2)⁻¹ : ℝ) := by
  simp [ghz4]


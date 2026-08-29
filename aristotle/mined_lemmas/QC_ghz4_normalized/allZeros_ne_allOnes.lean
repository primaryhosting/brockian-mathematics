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

lemma allZeros_ne_allOnes : (allZeros : Fin 4 → Fin 2) ≠ allOnes := by
  intro h
  have := congrFun h 0
  simp [allZeros, allOnes] at this

